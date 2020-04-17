#include <algorithm>
#include <boost/algorithm/string/trim.hpp>
#include <time.h>
#include "GlobalDef.h"
#include "Profile.h"
#include "XmlHttp.h"
#include "Config.h"
#include "TextAnalyzer.h"
#include "Searcher.h"
#include "Class.h"
#include "BitMap.h"
#include "Character.h"
#include "CharsetConvert.h"
#include "ExModule.h"
#include "FuzzyModule.h"
#ifdef _WIN32
#include "KeyRanking.h"
#include "MixReco.h"
#include "win_strptime.h"
#else 
#include "ShowTime.h"
#include <dirent.h>
#include <dlfcn.h>
#endif

#include <vector>
#include <csignal>

#include <fstream>

#include <unistd.h> /* read, write, close */
#include <sys/socket.h> /* socket, connect */
#include <netinet/in.h> /* struct sockaddr_in, struct sockaddr */

#include <sys/socket.h>
#include <arpa/inet.h>
#include "cJSON.h"
#include "Module.h"
#include "util/cJSON.h"
#include <boost/algorithm/string/trim.hpp>
#include <boost/algorithm/string.hpp>

using namespace std;
const int MIN_AND_RESULT=10;
const int MIN_OR_RESULT=10;
const int INC_FREQUENCY=100;
const int MAX_MARK_COUNT=1024*1024*128;
const int MAX_IMP_FIELD_RET_CNT=50000;
const int MAX_SCATTER_LIMIT=5000;

const int PRIMARY_KEY_INDEX = 0;


std::default_random_engine g_generator;
std::uniform_int_distribution<long> g_distribution(1, 32766);

#define INDEX_ADD     "_index_add"
#define INDEX_MODIFY  "_index_modify"
#define INDEX_DEL     "_index_del"
#define INDEX_RECOVER "_index_recover"
#define INDEX_OPT     "_index_opt"

#define INC_NUM       "_inc_num"
#define FORCE_UPDATE  "_force_update"
#define MODIFY_PREFIX "_modify_"

#define RELOAD_MODULE "_reload_module"
#define SHOW_MODULE   "_show_module"
#define SHOW_INFO   "_show_info"
#define SHOW_CONF   "_show_mconf"
#define MODIFY_VCONF "_modify_vconf"
#define SET_LOG_LEVEL "_set_log_level"

#define MODULES_DIR "modules"
#define LOG_DIR "log"
#define DEFAULT_RANKING "default_ranking"
#define KEYRANKING_DIR "key_ranking"
#define LISTRANKING_DIR "list_ranking"
#define FUZZYRANKING_DIR "fuzzy_ranking"
#define MIX_RECO_DIR    "mix_reco"
#define EG4KEYRANKING_DIR "eg4key_ranking"
#define DEL_MARK      "_del_mark"

#define VAR_CONF_FILE     ".var.conf"
#define BAK_VAR_CONF_FILE ".var.conf.bak"
#define MAX_PAGE_SIZE 300

#define SEARCH_DATA_CONF   "search_data.conf"
#define MODIFY_DEFAULT_MODULE "_DEFAULT_MODULE_"
#define MODIFY_URL "_ADD_URL_"
#define FORCE_MODIFY_URL "_FORCE_ADD_URL_"
#define DETAIL_FOR_MEMERY "_DETAIL_FOR_MEMERY_"
#define MATCH_DOC "_MATCH_DOC_"

#define SPLIT_EQ "="
#define SPLIT_COLON ":"

#define GRPC_DEFAULT_MAX_RECV_MESSAGE_LENGTH (1 * 1024 * 1024)

const char* UTF8_FMT = "utf8";
const char* GBK_FMT = "gbk";

clock_t CSearcher::s_last_update_ee_ = std::clock();
bool CSearcher::s_firsttime = true;
#define UPDATE_FALSE_RETURN(clause,code,inc)  if(clause) {write_log_open_version(&m_slog, true, L_ERROR, \
                                           __FILE__, __LINE__, "inc num: %d, error info: %s", inc, strerror(errno)); SetIncFail(); return code;}

#define COMMON_FALSE_RETURN(clause)   if(clause) { write_log_open_version(&m_slog, true, L_ERROR, \
	                               __FILE__, __LINE__, "error info: %s", strerror(errno));return false;}

#define _COMMON_LOG(level, fmt, ...)  (write_log_open_version(&m_slog, true, level, __FILE__, __LINE__,  fmt, ##__VA_ARGS__));
#define _SESSION_LOG(level, fmt, ...)  (write_log_open_version(&m_slog, false, level, __FILE__, __LINE__,  fmt, ##__VA_ARGS__));


enum 
{
	  OK, 
	  INC_NUM_MISS,
	  INC_NUM_LOW,
	  FULL_TM_MISS,
	  FULL_TM_ERROR,
      NOT_AFFECTED,
	  SYNC_ERROR,
      PROFILE_ADD_ERROR,
      INDEX_ADD_ERROR,
      DETAIL_ADD_ERROR,
	  INC_FROZEN,
	  OTHER_ERROR
};

static const char* g_updateInfo[]=
{
	"OK",
	"FAIL-1:INC_NUM_MISS",
	"FAIL-2:INC_NUM_LOW",
	"FAIL-3:FULL_TM_MISS",
	"FAIL-4:FULL_TM_ERROR",
	"WARN-5:NOT_AFFECTED",
	"FAIL-6:SYNC_ERROR",
	"FAIL-7:PROFILE_ADD_ERROR",
	"FAIL-8:INDEX_ADD_ERROR",
	"FAIL-9:DETAIL_ADD_ERROR",
	"FAIL-10:INC_FROZEN",
	"FAIL-11:OTHER_ERROR"
};

enum 
{
	RELOAD_OK,
	MODULE_MISS_TM,
	MODULE_NOT_SUPPORT,
	MODULE_INIT_FAIL
};

static const char* g_reloadInfo[]=
{
	"OK",
	"FAIL-1:MODULE_MISS_TM",
	"FAIL-2:MODULE_NOT_SUPPORT",
	"FAIL-3:MODULE_INIT_FAIL"
};
static const char *g_log_level[] = {
	"0:DEBUG",
	"1:INFO",
	"2:NOTICE",
	"3:WARN",
	"4:ERROR",
	"5:CRIT",
	"6:FATAL"
};
const int g_timeSpanRuler[]={0,1,2,2,2,3,3,3,3,3,4};
const char* g_timeTitle[]={"0  ~ 10  ",
							"10 ~ 20  ",
							"20 ~ 50  ",
							"50 ~ 100 ",
							"100~     "};
CharacterConverter gs_cc;
static string& operator+=(string& str, int num)
{
	char buf[32];
	sprintf(buf,"%d",num);
	return str+=buf;
}

static u64 Mul(u64 a, u64 b)
{
	return b==0? 0:a/b;
}


CTextAnlyzer  g_analyzer;
VAR_SET g_var_set;


void GetDocDataOpenApi(int nDocId, vector<int>& vShowFieldIds, 
					   vector<char*>& vFieldDataPtr, 
					   vector<char>& vDataBuf, void* pSearcher);
void GetDocsByPkOpenApi(void* pSearcher, int fid, 
						vector<long long>& vPk, vector<int>& vDocIds);

void ScatterResultOpenApi(void* pSearcher, vector<SResult>& res,
						  vector<int>& pri, int fid, int unit,int sort_upper);

void GetTermInfoOpenApi(string& key,vector<string>& vFinalTerms);
void GetTermWeightOpenApi(void* pSearcher,vector<string>& vKeys,vector<Term>& vTerms);
void GetIdfOpenApi(void* pSearcher,map<string,float>& mTerms,string& type);

inline bool CSearcher::ParseConf(const string& file)
{
	ifstream fin(file.c_str());
	if(!fin) return false;
	string line = "";
	vector<string> vPara;
	vector<string> vKey;
	CXmlHttp xh;
	while(getline(fin,line))
	{
		vKey.clear();
		vPara.clear();
		HSS hssParse;
		SplitToVecEx<string>((char*)(line.c_str()),vPara,SPLIT_COLON);
		//if(vPara.size() != 2) continue;
		SplitToVecEx<string>((char*)(vPara[0].c_str()),vKey,SPLIT_EQ);
		if(vKey.size() != 2) continue;
		if(vKey[0] == MODIFY_DEFAULT_MODULE)
		{
			m_defaultModule = vKey[1];
		}
		else if(vKey[0] == MODIFY_URL)
		{
			xh.ParseRequest(vPara[1],hssParse);
			m_addUrlHash.insert(make_pair(vKey[1],hssParse));
		}
		else if(vKey[0] == FORCE_MODIFY_URL)
		{
			xh.ParseRequest(vPara[1],hssParse);
			m_forceAddUrlHash.insert(make_pair(vKey[1],hssParse));
		}
        else if(vKey[0] == DETAIL_FOR_MEMERY)
        {
            m_bMem=atoi(vKey[1].c_str());
        }
        else if(vKey[0] == MATCH_DOC)
        {
            m_bMatch=atoi(vKey[1].c_str());
        }
	}
	fin.close();
	return true;
}

void CSearcher::ModifyUrlPara(HSS &hssParseRes)
{
	if(hssParseRes.find(UM) == hssParseRes.end())
		hssParseRes.insert(make_pair(UM,m_defaultModule));
	if(hssParseRes.find(UM) != hssParseRes.end())
	{
		HSS hssUrl;
		HSSI it;
		string module = hssParseRes[UM];
		//扩展参数
		if(m_addUrlHash.find(module) != m_addUrlHash.end())
		{
			hssUrl = m_addUrlHash[module];
			for(it = hssUrl.begin(); it != hssUrl.end(); it++)
			{
				if(hssParseRes.find(it->first) == hssParseRes.end())
					hssParseRes.insert(*it);
			}
		}
		//修改参数
		if(m_forceAddUrlHash.find(module) != m_forceAddUrlHash.end())
		{
			hssUrl = m_forceAddUrlHash[module];
			for(it = hssUrl.begin(); it != hssUrl.end(); it++)
			{
				if(hssParseRes.find(it->first) == hssParseRes.end())
					hssParseRes.insert(*it);
				else
				   hssParseRes[it->first] = it->second;
			}
		}
	}
}

int CSearcher::CanBeUpdate(HSS& hssPara,int& inc)
{

	//should lock
	HSSI hssi;
	if((hssi=hssPara.find(INC_NUM))!=hssPara.end())
		inc=atoi(hssi->second.c_str());
	else
	{
		_COMMON_LOG(L_ERROR, "not found inc num");
		return INC_NUM_MISS;
	}

	if (inc<GetIncNum())
	{
		_COMMON_LOG(L_DEBUG, "invalid inc num %d,cur is %d",inc, GetIncNum());
		return INC_NUM_LOW;
	}

	int tms;
	if((hssi=hssPara.find(FULL_TM))!=hssPara.end())
		tms=atoi(hssi->second.c_str());
	else
	{
		_COMMON_LOG(L_ERROR, "not found full timestamp");
		return FULL_TM_MISS;
	}

	if (tms!=m_timestamp)
	{
		_COMMON_LOG(L_ERROR, "invalid full timestamp %d, cur is %d", tms, m_timestamp);
		return FULL_TM_ERROR;
	}

	return OK;

}

int CSearcher::ChangeDocMark(HSS& hssPara, bool bDel)
{
	int ret;
	int inc=0;
	HSSI hssi;
	bool bForce = true;
	if((hssi=hssPara.find(FORCE_UPDATE))==hssPara.end())
	{
		bForce = false;
		ret=CanBeUpdate(hssPara, inc);
		if (ret!=OK)
		{
			return ret;
		}
	}

	CControl ctl;
	vector<PSS> vpss;
	vector<PSS> vGP;
	vector<string> vRed;
	vector<SResult> vRank;

	SearchDocIDWithDel(hssPara,vRank,ctl,vGP,vRed,0);
	if(vRank.size()==0)
		return NOT_AFFECTED;


	if (m_nPK!=-1&&!bDel)
	{
		CProfile<CAnyType>* pfl=(CProfile<CAnyType>* )(m_vProfiles[m_nPK]);
		hash_map<long long,int> hm;
		hash_map<long long,int>::iterator it;
		long long pk;
		size_t i;
        int id;
		for (i=0;i<vRank.size();++i)
		{
			id=vRank[i].nDocId;
			if (pfl->m_nKeyPow == 3)
				pk=pfl->GetSingleLongLongVal(id);
			else if (pfl->m_nKeyPow == 2)
				pk=pfl->GetSingleIntVal(id);

			it=hm.find(pk);
			if (it!=hm.end())
				it->second<id ? it->second=id: true;
			else
				hm.insert(make_pair(pk,id));
		}
		int j=0;
		for(i=0;i<vRank.size();++i)
		{
			id=vRank[i].nDocId;
			if (pfl->m_nKeyPow == 3)
				pk=pfl->GetSingleLongLongVal(id);
			else if (pfl->m_nKeyPow == 2)
				pk=pfl->GetSingleIntVal(id);

			if (hm[pk]==id)
			{
				vRank[j]=vRank[i];
				++j;
			}
		}
		vRank.resize(j);
	}

	vector<char> vecAffectMark;
	vecAffectMark.resize(vRank.size(),0);

	bool bCurIsDel;
	for(size_t i=0;i<vRank.size();++i)
	{
		bCurIsDel=m_delMark.TestBit(vRank[i].nDocId);
		if (bCurIsDel==bDel)
			continue;

		bDel?
			m_delMark.SetBit(vRank[i].nDocId):
			m_delMark.ClearBit(vRank[i].nDocId);
		vecAffectMark[i]=1;
	}

	//class tree modify
	CProfile<long long>* p;
	int nDirect = (bDel?-1:1);
	for (size_t i=0;i<m_vFieldInfos.size();++i)
	{
		if (m_vFieldInfos[i].nSpecialType == CAT_FIELD)
		{
			p=(CProfile<long long>*)(m_vProfiles[i]);
			for (size_t j=0;j<vRank.size();++j)
			{
				if (vecAffectMark[j])
					p->DeleteOrRecoverDocForClassTree(vRank[j].nDocId, nDirect);
			}
		}
	}
	
	if (!bForce)
	{
		SetIncNum(inc+1);
		if (IncNumDiff()>=m_incFrequency && !Sync(inc+1))
		{
			SetIncFail();
			_COMMON_LOG(L_ERROR, "SYNC_ERROR inc num = %d", inc);
			return SYNC_ERROR;
		}
	}
	return OK;
}





int CSearcher::ModifyDoc(HSS& hssPara)
{

	int ret;
	int inc=0;
	HSSI hssi;
	bool bForce = true;
	if((hssi=hssPara.find(FORCE_UPDATE))==hssPara.end())
	{
		bForce = false;
		ret=CanBeUpdate(hssPara, inc);
		if (ret!=OK)
		{
			return ret;
		}
	}

	CControl ctl;
	vector<PSS> vpss;
	vector<PSS> vGP;
	vector<string> vRed;
	vector<SResult> vRank;
	HSS hssAddDoc;
	bool bFlag=false;
	SearchDocIDWithDel(hssPara,vRank,ctl,vGP,vRed,0);
	if(vRank.size()==0)
		return NOT_AFFECTED;
	vector<char*> vFieldDataPtr;
	vector<char> vDataBuf;
	if(m_vDtlFldIds.size() > 0)
		GetDocDataOpenApi(vRank.back().nDocId,m_vDtlFldIds,vFieldDataPtr,vDataBuf,this);

	string fName,fValue;
	int fid = 0;
	for(hssi=hssPara.begin();hssi!=hssPara.end();++hssi)
	{
		if(strncmp(hssi->first.c_str(),MODIFY_PREFIX, sizeof(MODIFY_PREFIX)-1)==0)
		{
			fName = hssi->first.c_str()+sizeof(MODIFY_PREFIX)-1;
			vpss.push_back(pair<string,string>(fName, hssi->second.c_str()));
			HSII hsii=m_hmFieldNameId.find(fName);
			size_t m = 0;
			for(;m<m_vDtlFldIds.size();++m)
			{
				fid=m_vDtlFldIds[m];
				if(m_vFieldInfos[fid].strFieldName == fName)
				{
					fValue = vFieldDataPtr[m];
					break;
				}
			}
			if(!bFlag&&hsii!=m_hmFieldNameId.end())
			{
				if(m_vFieldInfos[hsii->second].chDataType==STRING||
							m_vFieldInfos[hsii->second].nKeyPow==-1||m_vFieldInfos[hsii->second].nKeyCnt==0)
				{
					if(m == m_vDtlFldIds.size() || fValue != hssi->second)
						bFlag=true;
				}
			}
			hssAddDoc.insert(make_pair(hssi->first.c_str()+sizeof(MODIFY_PREFIX)-1,hssi->second.c_str()));
		}
	}
		
	for(size_t i=0;i<vpss.size();++i)
	{
		hssi=hssPara.find(string(MODIFY_PREFIX)+vpss[i].first);
		if(hssi!=hssPara.end())
			hssPara.erase(hssi);
	}

	//wqf add
	if(bFlag)
	{
		int fid=0;
		string sName;
		for(size_t m=0;m<m_vDtlFldIds.size();++m)
		{
			fid=m_vDtlFldIds[m];
			sName=m_vFieldInfos[fid].strFieldName;
			if(hssAddDoc.find(sName) == hssAddDoc.end())
				hssAddDoc.insert(make_pair(sName,vFieldDataPtr[m]));
		}
		hssPara.insert(make_pair(FORCE_UPDATE,"1"));
		ret=ChangeDocMark(hssPara,true);
		hssPara[FORCE_UPDATE]="0";
		if(ret!=OK)
			return ret;
		hssAddDoc[INC_NUM]=hssPara[INC_NUM];
		hssAddDoc[FULL_TM]=hssPara[FULL_TM];
		ret=AddDoc(hssAddDoc);
		if(ret!=OK)
			return ret;
	}//end
	else
	{

		CProfile<char>* p;
		CProfile<short>* p1;
		CProfile<int>* p2;
		CProfile<long long>* p3;
		char chTmBuf[32];
		struct tm tm;
		for(size_t j=0;j<vpss.size();++j)
		{
			CProfile<CAnyType>* pfl;
			HSII hsii=m_hmFieldNameId.find(vpss[j].first.c_str());
			if (hsii==m_hmFieldNameId.end()|| (pfl = (CProfile<CAnyType>*)(m_vProfiles[hsii->second]))==NULL)
				continue;

			if(pfl->m_nKeyPow<0||pfl->m_nKeyCnt==0)
				continue;
			if (pfl->m_fi.nSpecialType == DATE_TIME_FIELD)
			{
				if(!vpss[j].second.empty())
				{
					strptime(vpss[j].second.c_str(), DATE_FORMAT, &tm);
					sprintf(chTmBuf, "%lld", (long long)mktime(&tm));
					vpss[j].second = chTmBuf;
				}
				else
					vpss[j].second = "0";
			}
			for(size_t i=0;i<vRank.size();++i)
			{
				switch(pfl->m_nKeyPow)
				{
					case 0:
						p = (CProfile<char>*)pfl;
						p->SetFixLenVal(vRank[i].nDocId, vpss[j].second.c_str());
						break;
					case 1:
						p1 = (CProfile<short>*)pfl;
						p1->SetFixLenVal(vRank[i].nDocId, vpss[j].second.c_str());
						break;
					case 2:
						p2 = (CProfile<int>*)pfl;
						p2->SetFixLenVal(vRank[i].nDocId, vpss[j].second.c_str());
						break;
					case 3:
						p3 = (CProfile<long long>*)pfl;
						p3->SetFixLenVal(vRank[i].nDocId, vpss[j].second.c_str());
						break;
				}
			}
		}
	}

	if (!bForce)
	{
		SetIncNum(inc+1);
		if (IncNumDiff()>=m_incFrequency && !Sync(inc+1))
		{
			SetIncFail();
			_COMMON_LOG(L_ERROR, "SYNC_ERROR inc num = %d", inc);
			return SYNC_ERROR;
		}
	}
	return OK;
}




int CSearcher::AddDoc(HSS& hssDoc)
{
	int ret;
	int inc;
	HSSI hssi;
	ret=CanBeUpdate(hssDoc,inc);
	if (ret!=OK)
	{
		return ret;
	}

	//del by primary key
	if (m_nPK != -1)
	{
		HSS hssDel;
		hssDel[FORCE_UPDATE] = 1; 
		HSSI itPk = hssDoc.find(m_vFieldInfos[m_nPK].strFieldName);
		if (itPk != hssDoc.end() && !itPk->second.empty())
		{
			//no effect ||modify || add
			HSS hpk;
			HSS hModifyDoc;
			HSS hPureDoc;
			CControl ctl;
			vector<PSS> vpss;
			vector<PSS> vGP;
			vector<string> vRed;
			vector<SResult> vRank;
			hpk.insert(*itPk);
			SearchDocID(hpk,vRank,ctl,vGP,vRed,0);
			if (vRank.size())
			{

				int fid=0;
				string sName;
				vector<char> vDataBuf;
				vector<char*> vFieldDataPtr;
				if(m_vDtlFldIds.size() > 0)
					GetDocDataOpenApi(vRank.back().nDocId,m_vDtlFldIds,vFieldDataPtr,vDataBuf,this);

				for (size_t i=0;i<m_vFieldInfos.size();++i)
				{
					SFieldInfo &fi=m_vFieldInfos[i];
					hssi=hssDoc.find(fi.strFieldName);
					if (hssi!=hssDoc.end())
						hPureDoc.insert(*hssi);
				}

				for(size_t m=0;m<m_vDtlFldIds.size();++m)
				{
					fid=m_vDtlFldIds[m];
					sName=m_vFieldInfos[fid].strFieldName;
					hssi = hPureDoc.find(sName) ;
					if (hssi != hPureDoc.end() && hssi->second == vFieldDataPtr[m])
						hPureDoc.erase(hssi);
				}

				if (hPureDoc.empty())/////////not affected return
					return NOT_AFFECTED;

				for (hssi = hPureDoc.begin(); hssi != hPureDoc.end(); ++hssi)
				{
					if (m_hmFieldNameId.find(hssi->first)!=m_hmFieldNameId.end())
						fid = m_hmFieldNameId[hssi->first];
					if(m_vFieldInfos[fid].chDataType==STRING||
						m_vFieldInfos[fid].nKeyPow==-1||
						m_vFieldInfos[fid].nKeyCnt==0||
						m_vFieldInfos[fid].bProfile == false)
						break;
				}

				if (hssi == hPureDoc.end()) //go to modify
				{
					hModifyDoc[INC_NUM]=hssDoc[INC_NUM];
					hModifyDoc[FULL_TM]=hssDoc[FULL_TM];
					for (hssi = hPureDoc.begin(); hssi != hPureDoc.end(); ++hssi)
						hModifyDoc.insert(make_pair(string(MODIFY_PREFIX)+hssi->first, hssi->second));
					hModifyDoc.insert(*itPk);
					
					return ModifyDoc(hModifyDoc);

				}
			}


			hssDel.insert(*itPk);
			ChangeDocMark(hssDel, true);
		}
		else 
			return  NOT_AFFECTED;
	}	
	int nNewId=GetNewDocId();
	const char *ptr;
	vector<char> vecDocDtl;
	int nReserveSz=0;
	for (HSSI it=hssDoc.begin();it!=hssDoc.end();++it)
		nReserveSz+=it->second.size();
	vecDocDtl.reserve(nReserveSz+512);

	char chTmBuf[32];
	struct tm tm;
	for (size_t i=0;i<m_vFieldInfos.size();++i)
	{
		
		SFieldInfo &fi=m_vFieldInfos[i];
		hssi=hssDoc.find(fi.strFieldName);
		if (hssi!=hssDoc.end()&&hssi->second.length())
		{
			ptr=hssi->second.c_str();
			if (fi.bShow)
				vecDocDtl.insert(vecDocDtl.end(),ptr,ptr+strlen(ptr)+1);
		}
		else
		{
			ptr="";
			if (fi.bShow)
				vecDocDtl.push_back('\0');
		}


		if (fi.chDataType==STRING)
		{
		
			if (m_vFieldIndexes[i])
			{
				UPDATE_FALSE_RETURN(!((CImplIndex<string,int>* )(m_vFieldIndexes[i]))->AddIndex(ptr,nNewId,inc),INDEX_ADD_ERROR,inc);
			}
			if (m_vTextIndexes[i])
			{
				UPDATE_FALSE_RETURN(!((CImplIndex<string,SIvtNode>* )(m_vTextIndexes[i]))->AddIndex(ptr,nNewId,inc),INDEX_ADD_ERROR,inc);
			}
		}
		else
		{
			CProfile<char>* p;
			CProfile<short>* p1;
			CProfile<int>* p2;
			CProfile<long long>* p3;
			string str1,str2;
			if (fi.nSpecialType == CAT_FIELD)
			{
				vector<u64> vCls;
				TransePathes2ClsIds(ptr,vCls);
				p3=(CProfile<long long>*)(m_vProfiles[i]);
				if (vCls.size())
					p3->ModifyClassTree(&vCls[0], vCls.size(), 1);
				TransePathes2ClsIdsNoExpend(ptr, str1);
				TransePathes2ClsIds(ptr, str2);
			} 
			else if (fi.nSpecialType == DATE_TIME_FIELD)
			{
				if(!(*ptr))
					ptr = "0";
				else
				{
					strptime(ptr, DATE_FORMAT, &tm);
					sprintf(chTmBuf, "%lld", (long long)mktime(&tm));
					ptr=chTmBuf;
				}
			}

			switch(fi.nKeyPow)
			{				
			case 0:
				if (m_vProfiles[i])
				{
					p=(CProfile<char>*)(m_vProfiles[i]);
					UPDATE_FALSE_RETURN(-1==p->AddProfile(nNewId,ptr),PROFILE_ADD_ERROR,inc);//
				}
				if (m_vFieldIndexes[i])
					UPDATE_FALSE_RETURN(!((CImplIndex<char,int>* )(m_vFieldIndexes[i]))->AddIndex(ptr,nNewId,inc),INDEX_ADD_ERROR,inc);
				break;
			case 1:
				if (m_vProfiles[i])
				{
					p1=(CProfile<short>*)(m_vProfiles[i]);
					UPDATE_FALSE_RETURN(-1==p1->AddProfile(nNewId,ptr),PROFILE_ADD_ERROR,inc);//
				}
				if (m_vFieldIndexes[i])
					UPDATE_FALSE_RETURN(!((CImplIndex<short,int>* )(m_vFieldIndexes[i]))->AddIndex(ptr,nNewId,inc),INDEX_ADD_ERROR,inc);
				break;
			case 2:
				if (m_vProfiles[i])
				{
					p2=(CProfile<int>*)(m_vProfiles[i]);
					UPDATE_FALSE_RETURN(-1==p2->AddProfile(nNewId,ptr),PROFILE_ADD_ERROR,inc);//
				}
				if (m_vFieldIndexes[i])
					UPDATE_FALSE_RETURN(!((CImplIndex<int,int>* )(m_vFieldIndexes[i]))->AddIndex(ptr,nNewId,inc),INDEX_ADD_ERROR,inc);
	
				break;
			case 3:
				if (m_vProfiles[i])
				{
					if (fi.nSpecialType == CAT_FIELD)
						ptr = str1.c_str();
					p3=(CProfile<long long>*)(m_vProfiles[i]);
					UPDATE_FALSE_RETURN(-1==p3->AddProfile(nNewId,ptr),PROFILE_ADD_ERROR,inc);//
				}
				if (m_vFieldIndexes[i])
				{
					if (fi.nSpecialType == CAT_FIELD)
						ptr = str2.c_str();
					UPDATE_FALSE_RETURN(!((CImplIndex<long long,int>* )(m_vFieldIndexes[i]))->AddIndex(ptr,nNewId,inc),INDEX_ADD_ERROR,inc);
				}
				break;
			default:			
				break;
			};
		}
	}
	
	if(vecDocDtl.size())
		UPDATE_FALSE_RETURN(!m_detail.WriteDetail(&vecDocDtl[0],vecDocDtl.size(),nNewId,m_bMem),DETAIL_ADD_ERROR,inc);
	m_delMark.ClearBit(nNewId);

	SetNextDocId(nNewId+1);
	SetIncNum(inc+1);
	if (IncNumDiff()>=m_incFrequency && !Sync(inc+1))
	{
		SetIncFail();
		_COMMON_LOG(L_ERROR, "SYNC_ERROR inc num = %d", inc);
		return SYNC_ERROR;
	}
	
	return OK;	
	//should unlock
}

bool CSearcher::Sync(int inc)
{

	for (size_t i=0;i<m_vFieldIndexes.size();++i)
	{
		if (m_vFieldIndexes[i]!=NULL)
		{
			if(!m_vFieldIndexes[i]->Sync(inc))
				return false;
		}
	}

	for (size_t i=0;i<m_vTextIndexes.size();++i)
	{
		if (m_vTextIndexes[i]!=NULL)
		{
			if(!(m_vTextIndexes[i])->Sync(inc))
				return false;
		}
	}

	for (size_t i=0;i<m_vProfiles.size();++i)
	{
		if (m_vProfiles[i]!=NULL)
		{
			((CProfile<CAnyType>*)(m_vProfiles[i]))->Sync();
		}
	}
	m_detail.Sync();
	m_delMark.Sync();
	RefreshUpIncInfo();
	return true;

}

bool CSearcher::ReadBaseTimeStamp(const char* file, int& tm)
{
	FILE* fp = fopen(file, "rb");
	COMMON_FALSE_RETURN(fp==NULL);
	COMMON_FALSE_RETURN(fread(&tm, sizeof(int), 1,fp)!=1);
	fclose(fp);
	return true;
}

//overfield 32 gap
SResult*  K_OverFieldIntersectNonOffet(vector<SIvtNode*>&vecNodePtr,
									 vector<SIvtNode*>&vecNodeEndPtr,
									 vector<Term>     &vecTerm,
									 vector<TIDX*> & vecIndex,
									 string          & strOrg,
									 SResult*        pNodeDest,
									 size_t              nMaxGetCnt,
									 vector<int>&    vGapAllow,
									 CModule*           pm,
									 IAnalysisData*     pad)

{

	//const int UCHARMAX=255;
	size_t i,j;
	if (vecNodePtr.empty()||vecNodePtr.size()==1)
	{
		return pNodeDest;
	}
	for (j=0;j<vecNodePtr.size();++j)
	{
		if (vecNodePtr[j]==vecNodeEndPtr[j])
		{
			return pNodeDest;
		}				
	}

	size_t stMatchLimit=0;


	SMatchElement sme;
	sme.matchType = OVER_FIELD_MATCH;
	sme.vTerms = vecTerm;
	sme.vAllowGap = vGapAllow;
	sme.vFieldsOff.resize(vecNodePtr.size());
	sme.vFieldLen.resize(vecTerm.size());
	sme.vTf.resize(vecTerm.size());
	sme.vIdf.resize(vecTerm.size());


	//int fid;
	string str;
	vector<vector<int> > vvTf(vecTerm.size());
	vector<vector<float> > vvIdf(vecTerm.size());
	for (i=0;i<vecTerm.size();++i)
	{
		vvTf[i].resize(vecIndex.size());
		vvIdf[i].resize(vecIndex.size());
	}
	for (i=0;i<vecTerm.size();++i)
	{
		str=strOrg.substr(vecTerm[i].pos, vecTerm[i].len);
		for (j=0;j<vecIndex.size();++j)
		{
			if (vecIndex[j]==NULL)
				continue;
			vvTf[i][j]=vecIndex[j]->GetTf(str);
			vvIdf[i][j]=vecIndex[j]->GetIdf(str);
		}
	}


	vector<SIvtNode*> vecCurColMark=vecNodePtr;
	//SIvtNode *pCurNode;
	//SIvtNode *pEndNode;
	//bool bSuccess;
	//int nAccGap=0;
	//int nTotalGap=0;
	SIvtNode* p;
	SIvtNode* q;
	//int nAllowGap;
	int nDocId;
	int oldField;
	TIDX* pIdx;
	int nFid;

	while (true)
	{
		SIvtNode* pNode = vecCurColMark[0];
		sme.id = pNode->nDocId;
		oldField = pNode->uField;
		for (j=0;j<vecCurColMark.size();++j)
		{
			if (oldField!=vecCurColMark[j]->uField)
			{
				break;
			}
		}

		
		if(j!=vecCurColMark.size())//not all in same field
		{
			for (j=0;j<vecCurColMark.size();++j)
			{
				nFid=vecCurColMark[j]->uField;
				pIdx=vecIndex[nFid];
				sme.vFieldsOff[j].off =vecCurColMark[j]->nOffset;
				sme.vFieldsOff[j].field =vecCurColMark[j]->uField;
				sme.vTf[j]=vvTf[j][nFid];
				sme.vIdf[j]=vvIdf[j][nFid];
				sme.vFieldLen[j]=pIdx->GetFieldLen(sme.id);

			}
			pNodeDest->nDocId = sme.id;
			pm->ComputeWeight(pad, sme,*pNodeDest);
			++pNodeDest;
			if(++stMatchLimit==nMaxGetCnt)
				return pNodeDest;
		}
		
		nDocId = vecCurColMark[0]->nDocId;
		for (j=0;j<vecCurColMark.size();++j)
		{
			p=vecCurColMark[j];
			q=vecNodeEndPtr[j];
			while(p!=q&&p->nDocId==nDocId)
			{
				++p;
			}
			if (p==q)
				return pNodeDest;
			vecCurColMark[j]=p;
		}
		//nTotalGap=0;
	}
}

//先并集在交集
int CSearcher::SearchOverFields(vector<CTextQuery*>& vTextQuerys, vector<SResult>& vDocIds, CBitMap& bmForbidden, size_t nMaxGetCnt)
{

	if (vTextQuerys.size() < 2)
	{
		return 0;
	}
	int nSegType = 0;
	for(size_t i=0; i<vTextQuerys.size(); i++)
	{
		CImplIndex<string,SIvtNode>* pImp = vTextQuerys[i]->GetIndex();
		nSegType = pImp->GetSpecialType();
		if(nSegType == WORD_SEG_FIELD || nSegType == CHAR_SEG_FIELD)
			return 0;
	}
	CTextQuery* ptq;
	vector<vector<pair<SIvtNode*, SIvtNode*> > >vvIvt;
	vector<vector<SFetchInfo> > vvFI;
	vvIvt.resize(vTextQuerys.size());
	vvFI.resize(vTextQuerys.size());
	for (size_t i=0;i<vTextQuerys.size();++i)
	{
		ptq=vTextQuerys[i];
		ptq->GetIvtVec(vvIvt[i], vvFI[i]);
	}

	bool bCheck=vvIvt.size();
	
	for(size_t i=1;i<vvIvt.size();++i)
	{
		if (vvIvt[i].size()!=vTextQuerys[0]->GetSegTerm().size())
		{
			bCheck=false;
			break;
		}
	}

	if (bCheck)//every col has data
	{
		vector<char> vMark;
		vMark.resize((GetNewDocId()));
		int colsz=vvIvt[0].size();
		int rowsz=vvIvt.size();
		pair<SIvtNode*, SIvtNode*> pr;
		SIvtNode* p;
		int row,col;
		for (col=0;col<colsz;++col)
		{
			for(row=0;row<rowsz;++row)
			{
				pr=vvIvt[row][col];
				for (p=pr.first;p!=pr.second;++p)
				{
					if(vMark[p->nDocId]==col)
						++vMark[p->nDocId];
				}

			}
		}

		//row merge
		vector<vector<SIvtNode> > vvMerge;
		vector<vector<SIvtNode> > vvTemp;
		vector<SIvtNode*> vecNodePtr;
		vector<SIvtNode*> vecNodeEndPtr;
		vvMerge.resize(colsz);
		int nCnt;
		for (col=0;col<colsz;++col)
		{
			vvTemp.clear();
			vvTemp.resize(rowsz);

			for( row=0;row<rowsz;++row)
			{
				pr=vvIvt[row][col];
				vector<SIvtNode>& vTemp=vvTemp[row];
				for (p=pr.first;p!=pr.second;++p)
				{
					if (vMark[p->nDocId]==colsz)//match col ok
					{
						vTemp.push_back(*p);//
					}
				}
			}


			vecNodePtr.clear();
			vecNodeEndPtr.clear();
			vecNodePtr.resize(rowsz,NULL);
			vecNodeEndPtr.resize(rowsz,NULL);


			vector<SIvtNode >& vMergeRes=vvMerge[col];
			nCnt=0;	
			for (size_t i=0;i<vvTemp.size();++i)
			{
				if (!vvTemp[i].empty()) 
				{
					nCnt+=vvTemp[i].size();
					vecNodePtr[i]=&vvTemp[i].front();
					vecNodeEndPtr[i]=&vvTemp[i].back()+1;
				}
			}
			if (nCnt==0)//无结果返回
			{
				goto END;
			}


			vMergeRes.resize(nCnt);
			CWinnerTree<SIvtNode> wt(LESS_INVERT_NODE);			
			wt.CreateTree(vecNodePtr,vecNodeEndPtr,&vMergeRes[0]);
			wt.K_Merge(&vMergeRes[0]);

		}

		//intersect 

		vecNodePtr.clear();
		vecNodeEndPtr.clear();
		vecNodePtr.resize(colsz,NULL);
		vecNodeEndPtr.resize(colsz,NULL);
		for (col=0;col<colsz;++col)
		{
			vecNodePtr[col]=&(vvMerge[col][0]);
			vecNodeEndPtr[col]=vecNodePtr[col]+vvMerge[col].size();
		}
			
		if(vvMerge.empty())
		{
		  goto END;
		}
		vector<SResult> vRes;
		vRes.resize(vvMerge[0].size());

		SResult* prt;
		vector<TIDX*> vIndex;
		for (size_t i=0;i<m_vTextIndexes.size();++i)
		{
			vIndex.push_back((CImplIndex<string,SIvtNode>*)(m_vTextIndexes[i]));
		}
		
		int overCnt = m_overFieldMaxRet;
		prt=K_OverFieldIntersectNonOffet(vecNodePtr,vecNodeEndPtr,vTextQuerys[0]->GetSegTerm(),
                                         vIndex, vTextQuerys[0]->GetKey(),&(vRes[0]),overCnt,
										 vTextQuerys[0]->GetAllowGap(),vTextQuerys[0]->m_pm, vTextQuerys[0]->m_pad);
		vRes.resize(prt-&(vRes[0]));
		vector<SResult>::iterator itSrank=GroupBySomeMember(vRes.begin(), vRes.end(),EQUAL_RANK_ELE,MAX_RANK_SCORE_1FIELD);
		vRes.erase(itSrank,vRes.end());
		vector<SResult> vtmp = vDocIds;
		vDocIds.resize(vDocIds.size()+vRes.size());
		itSrank=set_union(vtmp.begin(),vtmp.end(), vRes.begin(), vRes.end(),vDocIds.begin(),LESS_RANK_ELE);
		vDocIds.erase(itSrank,vDocIds.end());
	}
END:

	for (size_t i=0;i<vTextQuerys.size();++i)
	{
		vTextQuerys[i]->PutIvtVec(vvFI[i]);
	}
    return 0;
}






int CSearcher::SearchAllTextField(vector<CTextQuery*>& vTextQuerys, vector<SResult>& vDocIds, CBitMap& bmForbidden, bool bFuzzy, int type, size_t nMaxGetCnt)
{
	vector<SResult*> vecNodePtr;
	vector<SResult*> vecNodeEndPtr;
	vecNodePtr.resize(vTextQuerys.size(),NULL);
	vecNodeEndPtr.resize(vTextQuerys.size(),NULL);
	int nTotalCnt=0;
	int nColMark=0;
	int nColValidCnt=0;
	
	for (size_t i=0;i<vTextQuerys.size() && nMaxGetCnt > 0;++i)//
	{
		vector<SResult>& vSIN=vTextQuerys[i]->DoTextQuery(bFuzzy,type,nMaxGetCnt,bmForbidden,GetNewDocId(),m_delMark,m_bMatch);
		_SESSION_LOG(L_DEBUG, "field id = %d weight = %d,get Cnt:%d",vTextQuerys[i]->GetIndex()->m_nFieldId,
                             vTextQuerys[i]->GetIndex()->m_nFTBaseWeight, vSIN.size());
        if(nMaxGetCnt<=vSIN.size())
            nMaxGetCnt=0;
        else
            nMaxGetCnt-=vSIN.size();

		if (!vSIN.empty())
		{
			nColMark=i;
			nColValidCnt++;
			nTotalCnt+=vSIN.size();
			vecNodePtr[i]=&vSIN.front();
			vecNodeEndPtr[i]=&vSIN.back()+1;
		}
		else if (vTextQuerys[i]->m_andOr == CQuery::AND)
		{
			return 0;
		}
	}

	if (nColValidCnt==0)
		return 0;
	else 
	{
		int nLastId=vDocIds.size();
		vDocIds.resize(nTotalCnt+vDocIds.size());
		
		if (nColValidCnt==1)
		{
			int k = nLastId;
			for (SResult*p=vecNodePtr[nColMark];p!=vecNodeEndPtr[nColMark];++p)
					vDocIds[k++]=*p;
		}
		else
		{
			if (vTextQuerys[0]->m_andOr == CQuery::OR)
			{
				CWinnerTree<SResult> wt(LESS_RANK_ELE);
				wt.CreateTree(vecNodePtr,vecNodeEndPtr,&vDocIds[nLastId]);
				if(wt.K_Merge(&vDocIds[nLastId])-&vDocIds[nLastId]!=nTotalCnt)
					_SESSION_LOG(L_DEBUG, "...............TextQuery Merge fail...........");
				vector<SResult>::iterator itSrank=GroupBySomeMember(vDocIds.begin()+nLastId,vDocIds.end(),EQUAL_RANK_ELE,MAX_RANK_SCORE_1FIELD);
				vDocIds.erase(itSrank,vDocIds.end());
			}
			else
			{
				SResult* pResEnd = K_Intersect<SResult>(vecNodePtr,vecNodeEndPtr,&vDocIds[nLastId],LESS_RANK_ELE,Add_TO_LEFT_NODE_SCORE);
				vDocIds.resize(vDocIds.size() - nTotalCnt +(pResEnd - &vDocIds[nLastId]));
			}
		}
			
		return vDocIds.size()-nLastId;
	}


}
/*
int CSearcher::SearchKeyWord(string& strKey,vector<SResult>& vDocWeight)
{
	vector<CTextQuery> vTxtQuery;
	for (size_t i=0;i<m_vTextIndexes.size();++i)
	{
		if(!m_vTextIndexes[i]) continue;
		vTxtQuery.push_back(CTextQuery());
		CTextQuery& tq=vTxtQuery.back();
		tq.m_andOr = CQuery::OR;
		tq.Prepare((CImplIndex<string,SIvtNode>*)m_vTextIndexes[i],strKey,GetNewDocId()-1);
	}
	vector<CTextQuery*> vTxtPQuery;
	int nTime=0;
	for (int i=0;i<vTxtQuery.size();++i)
	{
		vTxtPQuery.push_back(&vTxtQuery[i]);
	}
	SearchAllTextField(vTxtPQuery,vDocWeight,false,CTextQuery::FILED_MATCH,MAX_EXACT_SCORE_DOCS/10);

	if (vDocWeight.size()<MAX_EXACT_SCORE_DOCS/1000)	
	{
		++nTime;
		SearchAllTextField(vTxtPQuery,vDocWeight,true,CTextQuery::FILED_MATCH,MAX_FUZZY_SCORE_DOCS);
	}
	if(nTime==1)
	{
		stable_sort(vDocWeight.begin(),vDocWeight.end(),LESS_RANK_ELE);
		vDocWeight.erase(unique(vDocWeight.begin(),vDocWeight.end(),EQUAL_RANK_ELE),vDocWeight.end());
	}
	return vDocWeight.size();
}*/


int CSearcher::SearchOneTextField(const char* fieldName,string& strKey,vector<Term> vSegTerms,vector<SIvtNode>& vecRes,bool bFussy)
{
/*
	size_t nCnt=0;
	size_t nMinCnt;
	bool bGet;
	SIvtNode* pIvtNode;
	pair<SIvtNode*,SIvtNode*> pr;
	vector<SIvtNode*> vecNodePtr;
	vector<SIvtNode*> vecNodeEndPtr;
	CImplIndex<string,SIvtNode>* pTextIndex=NULL;

	for (int i=0;i<m_vFieldInfos.size();++i)
	{
		if (m_vFieldInfos[i].strFieldName==fieldName)
		{
			pTextIndex=(CImplIndex<string,SIvtNode>*)m_vTextIndexes[i];
		}
	}

	if (pTextIndex==NULL)
	{
		return 0;
	}

	nCnt=0;

	vector<SFetchInfo> vFI;//用于索引信息的内存管理
	vFI.resize(vSegTerms.size());

	bGet=true;
	nMinCnt=(size_t)(-1);
	size_t i;
	for (i=0;i<vSegTerms.size();++i)//对每个TERM获取倒排表
	{

		pr.first=pTextIndex->GetInvert(string(strKey.c_str()+vSegTerms[i].pos, vSegTerms[i].len),nCnt,vFI[i]);
		if (!pr.first||!nCnt) //该词无倒排跳出循环
		{
			bGet=false;
			break;
		}
		nMinCnt>nCnt?nMinCnt=nCnt:true;
		pr.second=pr.first+nCnt;
		vecNodePtr.push_back(pr.first); //存储倒排表的起始地址
		vecNodeEndPtr.push_back(pr.second);			//存储终止地址
	}

	if (bGet)//获得到倒排表
	{
		vecRes.resize(nMinCnt);//交集预留空间
		//纯粹交集精确匹配文档
		pIvtNode=bFussy?K_InvertIntersectNonOffet(vecNodePtr,vecNodeEndPtr,vSegTerms,&(vecRes[0]),1000000):
			K_InvertIntersectEx(vecNodePtr,vecNodeEndPtr,vSegTerms,&(vecRes[0]),1000000, true);
		vecRes.resize(pIvtNode-&(vecRes[0]));
	}

	for (i=0; i<vFI.size(); ++i)//还回倒排表给系统
		pTextIndex->PutInvert(vFI[i]);
	vecNodePtr.clear();
	vecNodeEndPtr.clear();
	*/
	return 0;

}

inline bool FieldImptanceCmp(CTextQuery* l, CTextQuery* r)
{
	return l->GetIndex()->m_nFTBaseWeight > r->GetIndex()->m_nFTBaseWeight;
}

void CSearcher::SynSearch(string& strKey, vector<SResult>& vRes, CBitMap& bmForbidden,CModule* pm)
{
	vector<CTextQuery*> vTQ;
	vector<int> vTQFid;

	SQueryClause sqc;
	sqc.cat = 0;
	sqc.bAdvance = false;
	sqc.firstSortId = -1;
	sqc.secondSortId = -1;
	for (size_t i=0;i<m_vTextIndexes.size();++i)
	{
		if(!m_vTextIndexes[i] || ((CImplIndex<string,SIvtNode>*)m_vTextIndexes[i])->m_nFTBaseWeight < IMPORTANT_FIELD_LIMIT)
			continue;
		CTextQuery* pQuery=new CTextQuery();
		pQuery->m_andOr = CQuery::OR;
		pQuery->Prepare((CImplIndex<string,SIvtNode>*)m_vTextIndexes[i],strKey,GetNewDocId()-1);
		vTQ.push_back(pQuery);		
		vTQFid.push_back(i);
	}
	sqc.key = strKey;

	if (vTQ.empty())
	{
		return ;
	}

	Term term;
	string stemp, sOrg;
	sqc.vTerms = vTQ[0]->GetSegTerm();
	sOrg=vTQ[0]->GetKey();
	sqc.vTermInFields.resize(sqc.vTerms.size());
	for (size_t i=0;i<sqc.vTerms.size();++i)
	{
		term=sqc.vTerms[i];
		stemp.assign(sOrg.c_str()+term.pos,term.len);
		for (size_t j=0;j<vTQ.size();++j)
		{
			if(vTQ[j]->GetKeyInDocCnt(stemp)>0)
				sqc.vTermInFields[i].push_back(vTQFid[j]);
		}
	}


	size_t i;                  
	IAnalysisData* pad = pm->QueryAnalyse(sqc);
	if (pad)
	{
		pad->bAdvance = sqc.bAdvance;
		for (i=0;i<vTQ.size();++i)
			vTQ[i]->SetQueryMethod(pm, pad);
		sort(vTQ.begin(),vTQ.end(), FieldImptanceCmp);
		SearchAllTextField(vTQ,vRes, bmForbidden, true,CTextQuery::FILED_MATCH,MAX_EXACT_SCORE_DOCS/1000);
		if (vRes.empty())
			SearchOverFields(vTQ, vRes,bmForbidden,500);
	}
	DeletePtrVec(vTQ);
	delete pad;
}

void CSearcher::FuzzySearch(string& strKey, vector<SResult>& vRes, CBitMap& bmForbidden, CModule* pFuzMod)
{
	vector<CTextQuery*> vTQ;
	vector<int> vTQFid;

	SQueryClause sqc;
	sqc.cat = 0;
	sqc.bAdvance = false;
	sqc.firstSortId = -1;
	sqc.secondSortId = -1;
	for(size_t i = 0; i < m_vTextIndexes.size(); ++i)
	{
		if(!m_vTextIndexes[i] || ((CImplIndex<string,SIvtNode>*)m_vTextIndexes[i])->m_nFTBaseWeight < FUZZY_FIELD_LIMIT)
			continue;
		CTextQuery* pQuery = new CTextQuery();
		pQuery->m_andOr = CQuery::OR;
		pQuery->Prepare((CImplIndex<string,SIvtNode>*)m_vTextIndexes[i], strKey, GetNewDocId()-1);
		pQuery->ComputeTermScore((CFuzzyModule*)pFuzMod);
		vTQ.push_back(pQuery);
		vTQFid.push_back(i);
	}
	sqc.key = strKey;

	if(vTQ.empty())
	{
		return;
	}

	Term term;
	string stemp, sOrg;
	sqc.vTerms = vTQ[0]->GetSegTerm();
	sOrg = vTQ[0]->GetKey();
	sqc.vTermInFields.resize(sqc.vTerms.size());
	for(size_t i = 0; i < sqc.vTerms.size(); ++i)
	{
		term = sqc.vTerms[i];
		stemp.assign(sOrg.c_str() + term.pos, term.len);
		for(size_t j = 0; j < vTQ.size(); ++j)
		{
			if(vTQ[j]->GetKeyInDocCnt(stemp) > 0)
				sqc.vTermInFields[i].push_back(vTQFid[j]);
		}
	}

	size_t i;                  
	IAnalysisData* pad = pFuzMod->QueryAnalyse(sqc);
	if(pad)
	{
		pad->bAdvance = sqc.bAdvance;
		for(i = 0; i < vTQ.size(); ++i)
			vTQ[i]->SetQueryMethod(pFuzMod, pad);
		sort(vTQ.begin(),vTQ.end(), FieldImptanceCmp);
		SearchAllTextField(vTQ, vRes, bmForbidden, true, CTextQuery::FILED_MATCH, 600);
	}
	DeletePtrVec(vTQ);
	delete pad;
}

static void LimitResult(int len, vector<SResult>& vTRes)
{
	if ( len > (int)vTRes.size())
		len = vTRes.size();
	SortRange(vTRes ,0, len);
	vTRes.resize(len);
	sort(vTRes.begin(), vTRes.end(), LESS_RANK_ELE);
}

static void SetSearchInfo(int type, int id, vector<SResult>& v)
{
	for (size_t j = 0; j < v.size(); ++j)
		SetSearchInfo(type, id, v[j].nWeight);
}

static void MergeToOrgDocList(int type, int id, vector<SResult>& vDocIds, vector<SResult>& vAppend)
{
	if (vAppend.empty())
		return;
	LimitResult(MIN_FIELD_MATCH/3, vAppend);
	SetSearchInfo(type, id, vAppend);
	vector<SResult>::iterator itSrank;
	vector<SResult> vtmp = vDocIds;
	vDocIds.resize(vDocIds.size()+vAppend.size());
	itSrank=set_union(vtmp.begin(),vtmp.end(), vAppend.begin(), vAppend.end(),vDocIds.begin(),LESS_RANK_ELE);
	vDocIds.erase(itSrank,vDocIds.end());
}



int CSearcher::MatchDoc(vector<CTextQuery*>& vTextQuerys,vector<CQuery*>& vFieldQuerys, 
						vector<SResult>& vDocWeight, int wantCnt, CModule* pMod)
{
	//int nTime=0;
	if (!vTextQuerys.empty())
	{

		CBitMap bmForbidden(GetNewDocId()+1000000);

		//按照重要性排序
		sort(vTextQuerys.begin(),vTextQuerys.end(), FieldImptanceCmp);
		vector<CTextQuery*> vImp;
		vector<CTextQuery*> vNImp;
		for (size_t i=0;i<vTextQuerys.size();++i)
		{
			if (vTextQuerys[i]->GetIndex()->m_nFTBaseWeight >= IMPORTANT_FIELD_LIMIT)
				vImp.push_back(vTextQuerys[i]);
			else
				vNImp.push_back(vTextQuerys[i]);
		}

		SearchAllTextField(vImp,vDocWeight, bmForbidden, true,CTextQuery::FILED_MATCH,wantCnt);
		_SESSION_LOG(L_DEBUG, "..........one field match %u",vDocWeight.size());


		if (vDocWeight.size() < MIN_FIELD_MATCH
			&& vTextQuerys.size()
			&& vTextQuerys[0]->m_andOr==CQuery::OR)
			//全文检索先各个重要字段然后在使用跨字段，然后非重要字段
		{
			
			size_t stBack=vDocWeight.size();
			if(pMod->IfOverFieldSearch() && vTextQuerys[0]->QueryCanBeOverField())
			{
				SearchOverFields(vImp, vDocWeight,bmForbidden,wantCnt - stBack);
				_SESSION_LOG(L_DEBUG, "..........over field match %u",vDocWeight.size()-stBack);
			}

			SearchAllTextField(vNImp,vDocWeight, bmForbidden, true,CTextQuery::FILED_MATCH,wantCnt - vDocWeight.size());
			//_SESSION_LOG(L_DEBUG, "..........non important field match %u",vDocWeight.size());
		}

		IAnalysisData* pad = vTextQuerys[0]->GetQueryAnalysisData();

		SetSearchInfo(0, 0, vDocWeight);
		if (vTextQuerys[0]->m_andOr==CQuery::OR //  ex search
			&& pMod &&pad && vDocWeight.size() < MIN_FIELD_MATCH)
		{
			string sExName = pad->m_hmUrlPara[EX_SEARCH_MODULE];
			CExModule* pExMod = NULL;
			MOD_MAP::iterator it;
			if ((it=m_mods.find(sExName))!=m_mods.end())
					pExMod = (CExModule*)(it->second.pMod);
			size_t osz = vDocWeight.size();
			if (pExMod)
			{
				vector<string> vSynonym;  //synnonym search
				string sOrgKey = vTextQuerys[0]->GetKey();
				pExMod->NeedSynSearch(vDocWeight, sOrgKey, pad->m_vTerms, vSynonym);
				pad->m_hmUrlPara[MIX_SEARCH_INFO] = "";
				
				vector<SResult> vTRes;
				//int len;
				for(size_t i = 0; i < vSynonym.size(); ++i)
				{
					vTRes.clear();
					SynSearch(vSynonym[i], vTRes, bmForbidden, pMod);
					MergeToOrgDocList(SYN_KEY,i, vDocWeight, vTRes);
					pad->m_hmUrlPara[MIX_SEARCH_INFO] += vSynonym[i];
					pad->m_hmUrlPara[MIX_SEARCH_INFO] += ",";
				}
				vTRes.clear();
				pExMod->Reco(sOrgKey, vDocWeight, vTRes, bmForbidden);
				MergeToOrgDocList(RECO_PRO, 0, vDocWeight, vTRes);
				if (osz != vDocWeight.size())
					pad->m_hmUrlPara[IS_MIX_SEARCH] = "1";
			}
			
		}
		if(vTextQuerys[0]->m_andOr == CQuery::OR && pMod &&
			pad && vDocWeight.size() == 0 && vTextQuerys[0]->GetSegTerm().size() <= 15)
		{
			CFuzzyModule* pFuzMod = NULL;
			MOD_MAP::iterator it;
			hash_map<string, string>::iterator mapIt;
			if((it = m_mods.find(FUZZYRANKING_DIR)) != m_mods.end())
				pFuzMod = (CFuzzyModule*)(it->second.pMod);
			bool sug = true, fuzzy = false;
			mapIt = pad->m_hmUrlPara.find("sug");
			if(mapIt != pad->m_hmUrlPara.end() && mapIt->second == "1")
				sug = false;
			mapIt = pad->m_hmUrlPara.find(FUZZY_SEARCH_MODULE);
			if(mapIt != pad->m_hmUrlPara.end() && mapIt->second == "1")
				fuzzy = true;
			size_t osz = vDocWeight.size();
			if(pFuzMod && sug && fuzzy)
			{
				string sOrgKey = vTextQuerys[0]->GetKey();
				vector<SResult> vTRes;
				FuzzySearch(sOrgKey, vTRes, bmForbidden, pFuzMod);
				MergeToOrgDocList(SYN_KEY, 0, vDocWeight, vTRes);
				if(osz != vDocWeight.size())
					pad->m_hmUrlPara[IS_FUZZY_SEARCH] = "1";
			}
		}
		if (vDocWeight.empty())
			return 0;
	}



	size_t i;
	int *pFQResBeg=NULL;
	int *pFQResEnd=NULL;
	if (!vFieldQuerys.empty())
	{
		vector<int*> vecNodePtr;
		vector<int*> vecNodeEndPtr;

		for (i=0;i<vFieldQuerys.size();++i)//任何一个字段搜不到则 RETURN 交集关系。
		{
			vector<int>& vi=vFieldQuerys[i]->DoFieldQuery();
			if (vi.empty())
			{
				vDocWeight.clear();
				return 0;
			}
			vecNodePtr.push_back(&vi.front());
			vecNodeEndPtr.push_back(&vi.back()+1);
		}

		pFQResEnd=K_Intersect<int>(vecNodePtr,vecNodeEndPtr,vecNodePtr[0],CMP_LESS_DEFAULT,NULL);
		pFQResBeg=vecNodePtr[0];
		if(pFQResEnd>pFQResBeg )
		{
			if (vTextQuerys.empty())//只是field query
			{
                vDocWeight.resize(pFQResEnd-pFQResBeg);
                for(i=0;i<vDocWeight.size();++i)
                    vDocWeight[i].nDocId=*pFQResBeg++;

			}
			else
			{
				SResult *pNode=&vDocWeight.front();
				SResult *pNodeF=&vDocWeight.front();
				SResult *pNodeL=&vDocWeight.back()+1;
				

				while (pNodeF!=pNodeL&&pFQResBeg!=pFQResEnd)
				{
					if (pNodeF->nDocId<*pFQResBeg) ++pNodeF;
					else if (*pFQResBeg<pNodeF->nDocId) ++pFQResBeg;
					else
					{
						*pNode=*pNodeF;
						++pNodeF;
						++pFQResBeg;
						++pNode;
					}
				}
				vDocWeight.resize(pNode-&vDocWeight[0]);
				

			}
		}
		else
		{
			vDocWeight.clear();
		}
	}


	if (!vTextQuerys.empty())
	{
		IAnalysisData* pad = vTextQuerys[0]->GetQueryAnalysisData();
		if (pMod&&pad&&(!pad->bAdvance || !pad->bAutoAd))
		{
			pMod->ReRanking(vDocWeight, pad);
		}
	}

	return vDocWeight.size();
}


template<class T>
class CFuncObj
{
public:
	CFuncObj(CProfile<CAnyType>* pfl, int nLessKind)
	{
		m_pfl=pfl;
		m_bLess=(nLessKind>0);
		m_b0Behind=(nLessKind==2);
	}

	inline bool operator()(const T& l,const T &r)
	{
		if (m_bLess)
		{
			if (m_b0Behind)
			{
				return m_pfl->ZeroBehindLessCmpFrstNumVal(l.nDocId,r.nDocId);
			}
			else
				return m_pfl->LessCmpFrstNumVal(l.nDocId,r.nDocId);
		}
		else
		{
			return m_pfl->GreatCmpFrstNumVal(l.nDocId,r.nDocId);
		}
	}

private:
	CProfile<CAnyType>* m_pfl;
	bool      m_bLess;
	bool      m_b0Behind;
};

template<class T>
class CFuncObjEx
{
public:
	CFuncObjEx(CProfile<CAnyType>* pf1,CProfile<CAnyType>* pf2,bool bLess1,bool bLess2)
	{
		m_pf1=pf1;
		m_pf2=pf2;
		m_bLess1=bLess1;
		m_bLess2=bLess2;
	}

	inline bool operator()(const T& l,const T &r)
	{
		if (m_bLess1)
		{
			if (m_bLess2)
			{
				return (m_pf1->LessCmpFrstNumVal(l.nDocId,r.nDocId))||
					(m_pf1->EqualCmpFrstNumVal(l.nDocId,r.nDocId)&&m_pf2->LessCmpFrstNumVal(l.nDocId,r.nDocId));
			}
			else
			{
				return (m_pf1->LessCmpFrstNumVal(l.nDocId,r.nDocId))||
					(m_pf1->EqualCmpFrstNumVal(l.nDocId,r.nDocId)&&m_pf2->GreatCmpFrstNumVal(l.nDocId,r.nDocId));
			}
		}
		else
		{	
			if (m_bLess2)
			{
				return (m_pf1->GreatCmpFrstNumVal(l.nDocId,r.nDocId))||
					(m_pf1->EqualCmpFrstNumVal(l.nDocId,r.nDocId)&&m_pf2->LessCmpFrstNumVal(l.nDocId,r.nDocId));

			}
			else
			{
				return (m_pf1->GreatCmpFrstNumVal(l.nDocId,r.nDocId))||
					(m_pf1->EqualCmpFrstNumVal(l.nDocId,r.nDocId)&&m_pf2->GreatCmpFrstNumVal(l.nDocId,r.nDocId));
			}

		}
	}
private:
	CProfile<CAnyType>* m_pf1;
	CProfile<CAnyType>* m_pf2;
	bool      m_bLess1;
	bool      m_bLess2;
};






template<class T>
inline int SortByOtherCondition(CSearcher* sr, CControl& ctl,vector<T>& vec,bool bPartial)
{
	CProfile<CAnyType>* pfl1=NULL;
	CProfile<CAnyType>* pfl2=NULL;
	if (ctl.nFSortId!=-1)
	{
		pfl1=(CProfile<CAnyType>* )(sr->m_vProfiles[ctl.nFSortId]);
	}
	if (ctl.nSSortId!=-1)
	{
		pfl2=(CProfile<CAnyType>* )(sr->m_vProfiles[ctl.nSSortId]);
	}
	if (!pfl1)
	{
		return 1;
	}


	if (!pfl2)
	{
		if (bPartial)
			SortRangeWithCFunc(vec,ctl.nF,ctl.nT,CFuncObj<T>(pfl1,ctl.nFSAsc));
		else
			stable_sort(vec.begin(),vec.end(),CFuncObj<T>(pfl1,ctl.nFSAsc));
	}
	else
	{
		if (bPartial)
			SortRangeWithCFunc(vec,ctl.nF,ctl.nT,CFuncObjEx<T>(pfl1,pfl2,ctl.nFSAsc,ctl.nSSAsc));
		else
			stable_sort(vec.begin(),vec.end(),CFuncObjEx<T>(pfl1,pfl2,ctl.nFSAsc,ctl.nSSAsc));
	}
	return 0;

}





void CSearcher::SortScore(CControl& ctrl, vector<SResult> &vResult, 
							int queryType, CModule* pMod, IAnalysisData* pad)
{
	if (vResult.empty())
	{
		return; 
	}
	

	//修正返回结果位置。
	size_t stStart;
	size_t stEnd;
	/*if (ctrl.usRetOff<1)
	{
		return ;
	}
	stStart=(ctrl.usRetOff-1)*ctrl.usRetCnt;*/

	stStart = ctrl.usRetOff;
	if((stStart>=vResult.size()))
	{
		return ;
	}
	stEnd=stStart+ctrl.usRetCnt;
	if(stEnd>vResult.size()){stEnd=vResult.size();}

	ctrl.nF=stStart;
	ctrl.nT=stEnd;
	//ctrl.usRetOff = stStart/ctrl.usRetCnt+1;
	//ctrl.usRetCnt = stEnd -stStart;

	if (ctrl.noSort!=0)
	{
		return;
	}

	if (!ctrl.strCustomSort.empty())
	{
		pMod->SortForCustom(vResult,ctrl.nF,ctrl.nT,pad);
	}
	else if (ctrl.nFSortId==-1)
	{
		if (GetPflFromName(ctrl.strScatterField.c_str()) != NULL)
		{
			vector<int> vtmp;
			ScatterResult(vResult, vtmp, m_hmFieldNameId[ctrl.strScatterField], ctrl.nScatterUnit, ctrl.nT);
		}
		else if (queryType>0)
		{
			pMod->SortForDefault(vResult,ctrl.nF,ctrl.nT,pad);
		} 
		else
		{
			//other sort by user just as text search ,may be modify
			pMod->SortForDefault(vResult,ctrl.nF,ctrl.nT,pad);
		}
	}
	else
	{

		if (ctrl.nSSortId==-1 && m_vFieldInfos[ctrl.nFSortId].nKeyPow<3)
		{
			CProfile<CAnyType>* pfl=(CProfile<CAnyType>* )(m_vProfiles[ctrl.nFSortId]);
			for (size_t i=0;i<vResult.size();++i)
			{
				vResult[i].nScore = ctrl.nFSAsc?  -pfl->GetSortVal(vResult[i].nDocId):
				                                  pfl->GetSortVal(vResult[i].nDocId);

			}
			if (pad->m_hmUrlPara[IS_MIX_SEARCH] == "1")
				sort(vResult.begin(),vResult.end(), MIX_SEARCH_COMPARE);
			else
				SortRange(vResult ,ctrl.nF, ctrl.nT);
			
		}
		else		
			SortByOtherCondition(this,ctrl,vResult,true);
	}

}
bool CSearcher::HaveQueryClause(HSS &hssParseRes)
{
	HSSI  hssi;
	HSII  hsii;
	for (hssi=hssParseRes.begin();hssi!=hssParseRes.end();++hssi)
	{
		if (hssi->first==TQ)
		{
			return true;
		}
		hsii=m_hmFieldNameId.find(hssi->first);
		if (hsii==m_hmFieldNameId.end())
			continue;
		if (m_vFieldInfos[hsii->second].chIndexType!=0);
			return true;
	}
	return false;
}

void CSearcher::GetFilterClause(vector<CFilter*>& vFilters,HSS &hssParseRes)
{
	const char* pName;
	const char* pRealName;
	HSSI hssi;
	HSII hsii;
	//bool bFilter;
	int nFieldId;
	int nKeyPow;
	void* pProfile;
	CFilter* pFilter;
	for (hssi=hssParseRes.begin();hssi!=hssParseRes.end();++hssi)
	{
		pName=hssi->first.c_str();
		string& strKey=hssi->second;
		if (strKey.empty())
			continue;
		if (strKey.length()>MAX_QUERY_KEY_LEN)
		{
			return ;
		}
		pRealName=pName;

		if(pName[0]=='-'||pName[0]=='_')
		{
			++pRealName;
		}
		else 
		{
			continue;
		}

		hsii=m_hmFieldNameId.find(pRealName);
		if (hsii==m_hmFieldNameId.end())
			continue;
		nFieldId=hsii->second;	
		char chDataType=m_vFieldInfos[nFieldId].chDataType;
		nKeyPow=m_vFieldInfos[nFieldId].nKeyPow;

		pProfile=m_vProfiles[nFieldId];
		if (pProfile==NULL)
			continue;
		if (chDataType==NUMBER)
		{
			switch(nKeyPow)
			{
			case 0:
				pFilter=new CImplFilter<char>;
				break;
			case 1:
				pFilter=new CImplFilter<short>;
				break;
			case 2:
				pFilter=new CImplFilter<int>;
				break;
			case 3:
				pFilter=new CImplFilter<long long>;
				break;
			};
		}
		else//为以后STRING 过滤做准备
		{

		}

		pFilter->Prepare(m_vFieldInfos[nFieldId].nSpecialType, pName[0]=='_', pProfile,strKey);
		vFilters.push_back(pFilter);
	}
	return ;
}

void CSearcher::GetCtlClause(CControl& ctrl, vector<PSS> &vGpName, HSS &hssParseRes)
{
	HSSI  hssi;
	HSII  hsii;
	const char*pName;
	vGpName.clear();


	if (hssParseRes.find(SC)!=hssParseRes.end())
	{
		ctrl.strScatterField = hssParseRes[SC];
		if (hssParseRes.find(SU)!=hssParseRes.end())
			ctrl.nScatterUnit = atoi(hssParseRes[SU].c_str());
		if (ctrl.nScatterUnit < 1 || ctrl.nScatterUnit > 20)
			ctrl.nScatterUnit = 1;
	}

	if (hssParseRes.find(SF)!=hssParseRes.end())
	{
		GetShowFieldIds(ctrl.vecShowFieldIds,hssParseRes[SF]);
	}

	for (hssi=hssParseRes.begin();hssi!=hssParseRes.end();++hssi)
	{
		if (hssi->first.length()==2)
		{
			pName=hssi->first.c_str();
			if (strcmp(PG,pName)==0)
				ctrl.usRetOff=atoi(hssi->second.c_str());
			else if(strcmp(PS,pName)==0)
				{ctrl.usRetCnt=atoi(hssi->second.c_str());if(ctrl.usRetCnt==0) ctrl.usRetCnt=1; if(ctrl.usRetCnt>MAX_PAGE_SIZE) ctrl.usRetCnt=MAX_PAGE_SIZE;}
			else if(strcmp(US,pName)==0)
				ctrl.strCustomSort=hssi->second;
			else if(strcmp(SS,pName)==0)
				ctrl.nSSortId=  (hsii=m_hmFieldNameId.find(hssi->second))==m_hmFieldNameId.end()? -1: hsii->second;
			else if(strcmp(FS,pName)==0)
				ctrl.nFSortId= (hsii=m_hmFieldNameId.find(hssi->second))==m_hmFieldNameId.end()? -1: hsii->second;
			else if(strcmp(FA,pName)==0)
				ctrl.nFSAsc=atoi(hssi->second.c_str());
			else if(strcmp(SA,pName)==0)
				ctrl.nSSAsc=atoi(hssi->second.c_str());
			else if(strcmp(ST,pName)==0)
				ctrl.nSearchType= atoi(hssi->second.c_str());
			else if(strcmp(NS,pName)==0)
				ctrl.noSort= atoi(hssi->second.c_str());
			else if(strcmp(GP,pName)==0)
			{
				string tmp=hssi->second;
				VS v;
				SplitToVec<string>((char*)tmp.c_str(),v);
				HSSI it;
				for (size_t k=0;k<v.size();++k)
				{
					//vGpName.push_back(make_pair<string,string>(v[k],""));
					vGpName.push_back(make_pair(v[k],""));
					if ((it=hssParseRes.find(v[k]))!=hssParseRes.end()||
						(it=hssParseRes.find(string("^")+v[k]))!=hssParseRes.end())
					{
						vGpName[k].second=it->second;
						if (vGpName[k].second.length())
							EnCnStrTolower((char*)vGpName[k].second.c_str());
					}
				}

			}
		}
	}
}
void CSearcher::GetShowFieldIds(vector<int>& vsf, const string& strShow)
{
	vector<string> vec;
	if (strShow.empty())
	{
		vsf=m_vDtlFldIds;
	}
	else
	{
		vector<char> vBuf(strShow.length()+1);
		memcpy(&vBuf[0], strShow.c_str(), strShow.length());
		vBuf[strShow.length()] ='\0';
		SplitToVecEx(&vBuf[0],vec,",");


		hash_map<string,int>::iterator it;
		for (size_t i=0;i<vec.size();++i)
		{
			it=m_hmFieldNameId.find(vec[i]);
			if(it!=m_hmFieldNameId.end()&&m_vFieldInfos[it->second].bShow)
			{
				vsf.push_back(it->second);
			}
		}
		sort(vsf.begin(),vsf.end());
		vsf.erase(unique(vsf.begin(),vsf.end()),vsf.end());
	}
	
}

void CSearcher::GetTermIdf(map<string,float>& mTerms,string& type)
{
    TIDX* tidx = (CImplIndex<string,SIvtNode>*)GetTextIdxFromName(type.c_str());
    if (tidx == NULL)
        return;
    
    map<string,float>::iterator it = mTerms.begin();
    for(;it != mTerms.end();++it)
    {
        string str = it->first;
        mTerms[str] = tidx->GetIdf(str);
    }
}

bool CSearcher::Parse(HSS &hssParseRes, vector<CFilter*>& vFilters, 
					  vector<CTextQuery*>& vTextQuerys, 
					  vector<CQuery*>& vFieldQuerys ,vector<PSS> &vGpName, 
					  IAnalysisData*& pad, CControl& ctrl, CModule*& pm)
{
	HSSI  hssi;
	HSII  hsii;
	if (hssParseRes.empty())
		return false;

	//parse query struct;
	SQueryClause sqc;
	sqc.cat = 0;
	sqc.bAdvance = false;
	sqc.firstSortId = -1;
	sqc.secondSortId = -1;
	sqc.hmUrlPara = hssParseRes;

	if (hssParseRes.find(SC)!=hssParseRes.end())
	{
		ctrl.strScatterField = hssParseRes[SC];
		if (hssParseRes.find(SU)!=hssParseRes.end())
			ctrl.nScatterUnit = atoi(hssParseRes[SU].c_str());
		if (ctrl.nScatterUnit < 1 || ctrl.nScatterUnit > 20)
			ctrl.nScatterUnit = 1;
	}

	if (hssParseRes.find(SF)!=hssParseRes.end())
		GetShowFieldIds(ctrl.vecShowFieldIds,hssParseRes[SF]);
	else
		ctrl.vecShowFieldIds=m_vDtlFldIds;

	vector<int> vTQFid;
	if ((hssi=hssParseRes.find(TQ))!=hssParseRes.end())//
	{
		for (size_t i=0;i<m_vTextIndexes.size();++i)
		{
			if(!m_vTextIndexes[i]) continue;
			CTextQuery* pQuery=new CTextQuery();
			pQuery->m_andOr = CQuery::OR;
			pQuery->Prepare((CImplIndex<string,SIvtNode>*)m_vTextIndexes[i],hssi->second,GetNewDocId()-1);
			vTextQuerys.push_back(pQuery);		
			vTQFid.push_back(i);
		}
		sqc.key = hssi->second;
	}
	

	const char *pName;
	const char *pRealName;
	bool bFilter=false;
	bool bAndOr=CQuery::OR;
	void* pProfile;
	CIndex*   pIndex;
	CQuery*   pQuery;
	CFilter* pFilter;
	int nFieldId;
	int nKeyPow;
	
	for (hssi=hssParseRes.begin();hssi!=hssParseRes.end();++hssi)
	{
		pName=hssi->first.c_str();

		string strKey=hssi->second;
		if (strKey.empty())
			continue;
		if (strKey.length()>MAX_QUERY_KEY_LEN)
		{
			return false;
		}
		if (strlen(pName)==2)
		{
			
			if (strcmp(PG,pName)==0)
				ctrl.usRetOff=atoi(hssi->second.c_str());
			else if(strcmp(PS,pName)==0)
				{ctrl.usRetCnt=atoi(hssi->second.c_str());if(ctrl.usRetCnt==0) ctrl.usRetCnt=1; if(ctrl.usRetCnt>MAX_PAGE_SIZE) ctrl.usRetCnt=MAX_PAGE_SIZE;}
			else if(strcmp(US,pName)==0)
				ctrl.strCustomSort=hssi->second;
			else if(strcmp(SS,pName)==0)
				{ctrl.nSSortId=  (hsii=m_hmFieldNameId.find(hssi->second))==m_hmFieldNameId.end()? -1: hsii->second;sqc.secondSortId=ctrl.nSSortId;}
			else if(strcmp(FS,pName)==0)
				{ctrl.nFSortId= (hsii=m_hmFieldNameId.find(hssi->second))==m_hmFieldNameId.end()? -1: hsii->second;sqc.firstSortId=ctrl.nFSortId;}
			else if(strcmp(FA,pName)==0)
				ctrl.nFSAsc=atoi(hssi->second.c_str());
			else if(strcmp(SA,pName)==0)
				ctrl.nSSAsc=atoi(hssi->second.c_str());
			else if(strcmp(ST,pName)==0)
				ctrl.nSearchType= atoi(hssi->second.c_str());
			else if(strcmp(NS,pName)==0)
				ctrl.noSort= atoi(hssi->second.c_str());
			else if(strcmp(GP,pName)==0)
			{
				string tmp=hssi->second;
				VS v;
				SplitToVec<string>((char*)tmp.c_str(),v);
				HSSI it;
				for (size_t k=0;k<v.size();++k)
				{
					//vGpName.push_back(make_pair<string,string>(v[k],""));
					vGpName.push_back(make_pair(v[k],""));
					if ((it=hssParseRes.find(v[k]))!=hssParseRes.end()||
					(it=hssParseRes.find(string("^")+v[k]))!=hssParseRes.end()||
					(it=hssParseRes.find(string("-")+v[k]))!=hssParseRes.end())
					{
						vGpName[k].second=it->second;
						if (vGpName[k].second.length())
							EnCnStrTolower((char*)vGpName[k].second.c_str());
						if (hssParseRes.find(string("-")+v[k])!=hssParseRes.end())
						{
							vGpName[k].second+="-";
						}
					}
				}
				
			}
			

		}
		else//肯定是查询或过滤字段了
		{
			pRealName=pName;
			bFilter=false;
			if(pName[0]=='-'||pName[0]=='_')
			{
				++pRealName;
				bFilter=true;
			}
			else if(pName[0]=='^')
			{
				++pRealName;
				bAndOr=CQuery::AND;
			}


			hsii=m_hmFieldNameId.find(pRealName);
			if (hsii==m_hmFieldNameId.end())
				continue;
			nFieldId=hsii->second;	
			char chDataType=m_vFieldInfos[nFieldId].chDataType;
			nKeyPow=m_vFieldInfos[nFieldId].nKeyPow;

			if (m_vFieldInfos[nFieldId].nSpecialType==CAT_FIELD)
			{
				u64 t=TranseClsPath2ID(strKey.c_str(), strKey.length());
				char buf[32];
				sprintf(buf,"%lld",t);
				strKey = buf;
				sqc.cat = t;
			}

			if (bFilter)
			{

				pProfile=m_vProfiles[nFieldId];
				if (pProfile==NULL)
					continue;
				pFilter=NULL;
				if (chDataType==NUMBER)
				{
					switch(nKeyPow)
					{
					case 0:
						pFilter=new CImplFilter<char>;
						break;
					case 1:
						pFilter=new CImplFilter<short>;
						break;
					case 2:
						pFilter=new CImplFilter<int>;
						break;
					case 3:
						pFilter=new CImplFilter<long long>;
						break;
					};
				}
				else//为以后STRING 过滤做准备
				{

				}

				if (pFilter)
				{
					pFilter->Prepare(m_vFieldInfos[nFieldId].nSpecialType, pName[0]=='_', pProfile, strKey);
					vFilters.push_back(pFilter);
				}

				
			}
			else //字段查询
			{
				if (m_vFieldInfos[nFieldId].chIndexType==TEXT_INDEX)//文本查询
				{
					//if(strKey.size()==2&&strKey[0]<0)
					//	continue;
				
					CTextQuery* pQuery=new CTextQuery();
					pQuery->m_andOr = CQuery::AND;
					pQuery->Prepare((CImplIndex<string,SIvtNode>*)m_vTextIndexes[nFieldId], strKey,GetNewDocId()-1);
					vTextQuerys.push_back(pQuery);
					sqc.bAdvance = true;
				}
				else//字段查询
				{
					pIndex=m_vFieldIndexes[nFieldId];
					if (pIndex==NULL)
						continue;
					pQuery=NULL;
					if (chDataType==STRING)
					{
						pQuery=new CFieldQuery<string>();
						((CFieldQuery<string>*)pQuery)->Prepare((CImplIndex<string,int>*)pIndex,strKey,GetNewDocId()-1);
					}
					else
					{
						switch (nKeyPow)
						{
						case 0:
							pQuery=new CFieldQuery<char>();
							((CFieldQuery<char>*)pQuery)->Prepare((CImplIndex<char,int>*)pIndex,strKey,GetNewDocId()-1);
							break;
						case 1:
							pQuery=new CFieldQuery<short>();
							((CFieldQuery<short>*)pQuery)->Prepare((CImplIndex<short,int>*)pIndex,strKey,GetNewDocId()-1);
							break;
						case 2:
							pQuery=new CFieldQuery<int>();
							((CFieldQuery<int>*)pQuery)->Prepare((CImplIndex<int,int>*)pIndex,strKey,GetNewDocId()-1);
							break;
						case 3:
							pQuery=new CFieldQuery<long long>();
							((CFieldQuery<long long>*)pQuery)->Prepare((CImplIndex<long long,int>*)pIndex,strKey,GetNewDocId()-1);
							break;
						};
					}

					
					if(pQuery)
					{
						pQuery->m_andOr=bAndOr;
						vFieldQuerys.push_back(pQuery);
					}

				}

			}

		}
	}

	if (!sqc.bAdvance)
	{
		if (vTextQuerys.size()>0)
		{
			Term term;
			string stemp, sOrg;
			sqc.vTerms = vTextQuerys[0]->GetSegTerm();
			sOrg=vTextQuerys[0]->GetKey();
			sqc.vTermInFields.resize(sqc.vTerms.size());
			for (size_t i=0;i<sqc.vTerms.size();++i)
			{
				term=sqc.vTerms[i];
				stemp.assign(sOrg.c_str()+term.pos,term.len);
				for (size_t j=0;j<vTextQuerys.size();++j)
				{
					if(vTextQuerys[j]->GetKeyInDocCnt(stemp)>0)
						sqc.vTermInFields[i].push_back(vTQFid[j]);
				}
			}

		}
	}
	else
	{
		for (size_t i=0;i<vTextQuerys.size();++i)
		{
			sqc.vvTerms.push_back(vTextQuerys[i]->GetSegTerm());
			sqc.vKeys4Advance.push_back(vTextQuerys[i]->GetKey());
			sqc.vFields4Advance.push_back(vTextQuerys[i]->GetIndex()->m_nFieldId);
		}

	}

	pm = pm->QueryClassify(sqc);//切换到其他模块

	size_t i;
	pad = pm->QueryAnalyse(sqc);
	pad->bAdvance = sqc.bAdvance;
	for (i=0;i<vTextQuerys.size();++i)
	{
		vTextQuerys[i]->SetQueryMethod(pm, pad);
	}
	for (i=0;i<vFieldQuerys.size();++i)
	{
		vFieldQuerys[i]->SetQueryMethod(pm, pad);
	}
	return true;
}

void* CSearcher::GetPflFromName(const char* str)
{
	HSII hsii=m_hmFieldNameId.find(str);
	if (hsii==m_hmFieldNameId.end())
		return NULL;
	return m_vProfiles[hsii->second];
}
CIndex* CSearcher::GetFieldIdxFromName(const char* str)
{
	HSII hsii=m_hmFieldNameId.find(str);
	if (hsii==m_hmFieldNameId.end())
		return NULL;
	return m_vFieldIndexes[hsii->second];
}
CIndex* CSearcher::GetTextIdxFromName(const char* str)
{
	HSII hsii=m_hmFieldNameId.find(str);
	if (hsii==m_hmFieldNameId.end())
		return NULL;
	return m_vTextIndexes[hsii->second];
}

string& CSearcher::RedText(const string& strIn, string& strOut, CDic_w &dic)
{

	VEC_PR_II vpii;
	dic.SearchKeyWordInDicEx((char*)strIn.c_str(), (char*)strIn.c_str()+strIn.length(), vpii);
	if (vpii.empty())
	{
		strOut=strIn;
		return strOut;
	}


	const char* ps=strIn.c_str();
	const char* pt=ps;
	for (size_t i=0;i<vpii.size();++i)
	{
		strOut+=string(pt, ps+vpii[i].first);
		strOut+="<font class=\"skcolor_ljg\">";
		strOut+=string(ps+vpii[i].first,ps+vpii[i].second);
		strOut+="</font>";
		pt=ps+vpii[i].second;
	}
	strOut+=string(ps+vpii.back().second,ps+strIn.length());
    return strOut;
}


void CSearcher::PackNumberToResult(const char* pDetail, string &strRes, int nDocId, CProfile<CAnyType>* pfl)
{
	if(pfl==NULL || pfl->m_nKeyCnt==0 )
	{
		strRes+=pDetail;
	}
	else
	{
		void* pVal=pfl->GetSingleNumVal(nDocId);//need support multikey
		char buf[32];
		switch(pfl->m_nKeyPow)
		{
		case 0:
			sprintf(buf, "%d",(int)(*(char*)pVal));
			break;
		case 1:
			sprintf(buf, "%d",(int)(*(short*)pVal));
			break;
		case 2:
			sprintf(buf, "%d",(int)(*(int*)pVal));
			break;
		case 3:
			sprintf(buf, "%lld",(long long)(*(long long*)pVal));
			break;
		}
		strRes+=buf;
	}
}

bool CSearcher::ShowResult(CControl& ctrl,GROUP_RESULT &vGpRes,vector<SResult>& vRes, vector<string>& vecRed, string& strRes)
{
	char chBuf[256];
	CXmlHttp xh;

	strRes+="<Header>";
	strRes+="<TotalCnt>";
	sprintf(chBuf,"%d",(int)vRes.size());
	strRes+=chBuf;
	strRes+="</TotalCnt>";

	strRes+="<Page>";
	sprintf(chBuf,"%d",ctrl.usRetOff);
	strRes+=chBuf;
	strRes+="</Page>";

	strRes+="<PageSize>";
	sprintf(chBuf,"%d",ctrl.usRetCnt);
	strRes+=chBuf;
	strRes+="</PageSize>";
	strRes+="</Header>";

	HSII hsii;
	//void*pProfile;
	string str;

	strRes+="<StatInfo>";
	
	for (size_t i=0;i<vGpRes.size();++i)
	{
		vector<SGroupByInfo> & vgb = vGpRes[i].second;
		strRes+="<"+m_vFieldInfos[vGpRes[i].first].strFieldName+">";

		for (size_t j=0;j<vgb.size();++j)
		{
			strRes+="<item id=\"";
			strRes+=vgb[j].bufId2str;
			strRes+="\" name=\"";
			xh.XmlEncode(vgb[j].bufName,strRes);
			strRes+="\" count=\"";
			sprintf(chBuf,"%d",vgb[j].nCnt);
			strRes+=chBuf;
			strRes+="\"/>";
		}
		strRes+="</"+m_vFieldInfos[vGpRes[i].first].strFieldName+">";
	}
	strRes+="</StatInfo>";

	
	const char* pDocDetail;
	string strName;

	//mark red......
	vector<string> vec=vecRed;
	sort(vec.begin(), vec.end());
	vec.erase(unique(vec.begin(), vec.end()),  vec.end());
	VEC_PR_SD vprsd;
	vprsd.reserve(vprsd.size());
	for(size_t i=0;i<vec.size();++i)
		vprsd.push_back(make_pair(vec[i], i));

	vprsd.erase(unique(vprsd.begin(),vprsd.end(),FOBJ_EqualBy1Mem<PSD,S>(offsetof(PSD,first))),vprsd.end());
	CDic_w dic;
	dic.LoadDicFromMem(vprsd,false);


	strRes+="<Body>";
	if (vRes.size())
	{
		CXmlHttp xh;
		string sRed;

		for (int i=ctrl.nF; i<ctrl.nT;++i)
		{
			SFetchInfo fi;
			pDocDetail=m_detail.GetData(vRes[i].nDocId,fi);
			if (!pDocDetail)
			{
				_SESSION_LOG(L_ERROR, "error info: %s", strerror(errno));
				continue;
			}


			strRes+="<Product>";
			strRes+="<DocId>";
			sprintf(chBuf,"%d",vRes[i].nDocId);
			strRes+=chBuf;
			strRes+="</DocId>";
			for (size_t j=0;j<m_vDtlFldIds.size();++j)
			{
				strName=m_vFieldInfos[m_vDtlFldIds[j]].strFieldName;
				strRes+="<";
				strRes+=strName;
				strRes+=">";
				if(m_vFieldInfos[m_vDtlFldIds[j]].chDataType!=NUMBER)
				{
					if (vecRed.empty())
					{
						xh.XmlPackText(pDocDetail,strRes);
					}
					else
					{
						sRed.clear();
						RedText(pDocDetail,sRed,dic);
						xh.XmlPackText(sRed.c_str(),strRes);
					}
				}
				else 
					PackNumberToResult(pDocDetail, strRes, vRes[i].nDocId, (CProfile<CAnyType>*)m_vProfiles[m_vDtlFldIds[j]]);
				strRes+="</";
				strRes+=strName;
				strRes+=">";
				pDocDetail+=strlen(pDocDetail)+1;

			}
			strRes+="</Product>";
			m_detail.PutData(fi);

		}
	}
	strRes+="</Body>";
	return true;
}



int CSearcher::SearchDocIDWithDel(HSS &hssParseRes, vector<SResult> &vDocs, CControl &ctrl,
						   vector<PSS>& vGPName, vector<string>& vHighLights,int wantCnt)
{
	vector<CFilter*> vF;
	vector<CTextQuery*> vTQ;
	vector<CQuery*> vFQ;
	IAnalysisData* pad;

	CModule* pUseMod=GetQueryUseModule(hssParseRes);
	pUseMod->QueryRewrite(hssParseRes);
	Parse(hssParseRes,vF,vTQ,vFQ,vGPName,pad,ctrl,pUseMod);
	if(!vTQ.empty()) 
		vTQ[0]->GetHighLights(vHighLights);
	MatchDoc(vTQ,vFQ,vDocs, wantCnt,NULL);

	if(vTQ.empty() && vFQ.empty() && !vF.empty())
	{
		int total = GetNewDocId();
		vDocs.resize(total);
		for(int i = 0;i < total;i++)
			vDocs[i].nDocId = i;
	}

	Filt(vF,vDocs);


	DeletePtrVec(vF);
	DeletePtrVec(vTQ);
	DeletePtrVec(vFQ);
	delete pad;
	return vDocs.size();
}



int CSearcher::SearchDocID(HSS &hssParseRes, vector<SResult> &vDocs, CControl &ctrl,
				 vector<PSS>& vGPName, vector<string>& vHighLights, int wantCnt)
{
	vector<CFilter*> vF;
	vector<CTextQuery*> vTQ;
	vector<CQuery*> vFQ;
	IAnalysisData* pad;
	CModule* pUseMod=GetQueryUseModule(hssParseRes);
	pUseMod->QueryRewrite(hssParseRes);
	Parse(hssParseRes,vF,vTQ,vFQ,vGPName,pad,ctrl,pUseMod);
	if(!vTQ.empty()) 
		vTQ[0]->GetHighLights(vHighLights);
	MatchDoc(vTQ,vFQ,vDocs,wantCnt,NULL);
	FiltInvalidDoc(vDocs);
	Filt(vF,vDocs);


	DeletePtrVec(vF);
	DeletePtrVec(vTQ);
	DeletePtrVec(vFQ);
	delete pad;
	return vDocs.size();
}

int CSearcher::FilterCurrentDoc(vector<SResult>& vec, HSS& hss)
{
	vector<CFilter*> vF;
	GetFilterClause(vF,hss);
	if (!vF.empty())
	{
		Filt(vF,vec);
	}
	DeletePtrVec(vF);
	return 0;
}

void CSearcher::GroupByOne(vector<int>& vRes, void* pProfile, string& sFilter, pair<int, vector<SGroupByInfo> >& prGpInfo)
{
	CProfile<char>* p;
	CProfile<short>* p1;
	CProfile<int>* p2;
	CProfile<long long>* p3;
	switch (((CProfile<CAnyType>*)pProfile)->m_nKeyPow)
	{
	case 0:
		p=(CProfile<char>*)pProfile;
		p->GroupBy(vRes,DEFAULT_GP_CNT,true,prGpInfo.second, sFilter);
		break;
	case 1:
		p1=(CProfile<short>*)pProfile;
		p1->GroupBy(vRes,DEFAULT_GP_CNT,true,prGpInfo.second, sFilter);
		break;
	case 2:
		p2=(CProfile<int>*)pProfile;
		p2->GroupBy(vRes,DEFAULT_GP_CNT,true,prGpInfo.second, sFilter);
		break;
	case 3:
		p3=(CProfile<long long>*)pProfile;
		p3->GroupBy(vRes,DEFAULT_GP_CNT,true,prGpInfo.second, sFilter);
		break;
	default:
		;//pProfile->StrTypeGroupBy(vRes,DEFAULT_GP_CNT,true,vgb, vGpName[i].second);
	}

}
/*
void CSearcher::GroupBy(vector<SResult>& vRes, vector<PSS>& vGpName, GROUP_RESULT& vGpRes)
{
	HSII hsii;
	
	void* pProfile;
	for (size_t i=0;i<vGpName.size();++i)
	{
		hsii=m_hmFieldNameId.find(vGpName[i].first);
		if (hsii==m_hmFieldNameId.end())
			continue;
		pProfile=m_vProfiles[hsii->second];
		if (pProfile==NULL)
			continue;
		vGpRes.push_back(make_pair(hsii->second, vector<SGroupByInfo>()));
		vector<SGroupByInfo>& vgb=vGpRes.back().second;
		CProfile<char>* p;
		CProfile<short>* p1;
		CProfile<int>* p2;
		CProfile<long long>* p3;

		switch (((CProfile<CAnyType>*)pProfile)->m_nKeyPow)
		{
		case 0:
			p=(CProfile<char>*)pProfile;
			p->GroupBy(vRes,DEFAULT_GP_CNT,true,vgb, vGpName[i].second);
			break;
		case 1:
			p1=(CProfile<short>*)pProfile;
			p1->GroupBy(vRes,DEFAULT_GP_CNT,true,vgb, vGpName[i].second);
			break;
		case 2:
			p2=(CProfile<int>*)pProfile;
			p2->GroupBy(vRes,DEFAULT_GP_CNT,true,vgb, vGpName[i].second);
			break;
		case 3:
			p3=(CProfile<long long>*)pProfile;
			p3->GroupBy(vRes,DEFAULT_GP_CNT,true,vgb, vGpName[i].second);
			break;
		default:
			;//pProfile->StrTypeGroupBy(vRes,DEFAULT_GP_CNT,true,vgb, vGpName[i].second);
		}
	}
}
*/
CModule* CSearcher::GetQueryUseModule(HSS& hssParseRes)
{
	CModule* pMod;
	HSSI i;
	MOD_MAP::iterator it;
	
	if ((i=hssParseRes.find(UM))!=hssParseRes.end())
	{
		if ((it=m_mods.find(i->second))!=m_mods.end())
		{
			pMod=it->second.pMod;
			hssParseRes.erase(i);
			return pMod;
		}
	}
	return m_mods[DEFAULT_RANKING].pMod;
}

void CSearcher::GetSuggestSearchFields(IAnalysisData* pad, const vector<CTextQuery*>& vOrg, vector<CTextQuery*>& vSuggest)
{
	if (pad)
	{
		if (pad->m_queryFieldIds.empty())
		{
			vSuggest = vOrg;
		}
		else
		{
			/*vector<int> vMark;
			vMark.resize(m_vFieldInfos.size(),0);
			for (int i=0;i<pad->m_queryFieldIds.size();++i)
			{
				vMark[pad->m_queryFieldIds[i]]=1;
			}
			vSuggest.reserve(vOrg.size());
			for(int i=0;i<vOrg.size();++i)
			{
				if (vMark[vOrg[i]->GetIndex()->m_nFieldId]==1)
				{
					vSuggest.push_back(vOrg[i]);
				}
			}*/
			vSuggest.reserve(vOrg.size());
			for(size_t i = 0; i < pad->m_queryFieldIds.size(); ++i)
			{
				for(size_t j = 0; j < vOrg.size(); ++j)
				{
					if(vOrg[j]->GetIndex()->m_nFieldId == pad->m_queryFieldIds[i])
					{
						vSuggest.push_back(vOrg[j]);
						break;
					}
				}
			}
		}
		int nFid;
		for (size_t i=0;i<vSuggest.size();++i)
		{
			nFid = vSuggest[i]->GetIndex()->m_nFieldId;
			_SESSION_LOG(L_DEBUG, "suggest search field_id = %d, name = %s",  
				nFid, m_vFieldInfos[nFid].strFieldName.c_str());
		}
	}
}

void CSearcher::InitFiltAndGroupBySequence(vector<CFilter*> vFilters, vector<PSS>& vGpName, vector<SFGNode>& vFgn)
{
	HSII hsii;
	void* pProfile;
	vFgn.reserve(vFilters.size()+vGpName.size());
	SFGNode fgn;
	fgn.nId=0;
	fgn.sgpf.nMax=-1;
	fgn.sgpf.nMin=-1;
	fgn.sgpf.nNot=0;
	fgn.sgpf.nPflId=-1;
	fgn.sgpf.nCatlimit=-1;

	for (size_t i=0;i<vFilters.size();++i)
	{
		fgn.nType=SFGNode::FILT_TYPE;
		fgn.nCid=i;
		fgn.nField=vFilters[i]->GetFiltFieldId();
		vFgn.push_back(fgn);
		++fgn.nId;
	}

	for(size_t i=0;i<vGpName.size();++i)
	{

		hsii=m_hmFieldNameId.find(vGpName[i].first);
		if (hsii==m_hmFieldNameId.end())
			continue;
		pProfile=m_vProfiles[hsii->second];
		if (pProfile==NULL)
			continue;
		fgn.nType=SFGNode::GROUPBY_TYPE;
		fgn.nCid=i;
		fgn.nField=hsii->second;
		vFgn.push_back(fgn);
		++fgn.nId;
	}

	

}
void CSearcher::FiltAndGroupBy(CModule* pMod, IAnalysisData* pad, vector<SFGNode>& vFgn,vector<SResult>& vDocIds,
							   vector<CFilter*>& vFilters,vector<PSS>& vGpName, GROUP_RESULT& vGpRes)
{
	if (vFgn.empty())
		return ;
	vector<int> vSimpleIds(vDocIds.size());
	size_t i,j,k;
	for (j=0;j<vDocIds.size();++j)
	{
		vSimpleIds[j]=vDocIds[j].nDocId;
	}
	
	
	HSII hsii;
	void* pProfile;
	int nCid;
	for(size_t i=0;i<vFgn.size();++i)
	{
		if(vFgn[i].nCid < 0)
		{
			if (vFgn[i].nType ==SFGNode::FILT_TYPE)
			{
				pMod->CustomFilt(pad,vSimpleIds, vFgn[i]);
			}
			else if (vFgn[i].nType ==SFGNode::GROUPBY_TYPE)
			{
				vGpRes.resize(vGpRes.size()+1);
				pMod->CustomGroupBy(pad, vSimpleIds, vFgn[i], vGpRes.back());
			}
		}
		else
		{
			nCid=vFgn[i].nCid;
			if (vFgn[i].nType ==SFGNode::FILT_TYPE)
			{
				if (nCid>=0 && nCid<(int)vFilters.size())
					vFilters[nCid]->Filt(vSimpleIds);
			}
			else if (vFgn[i].nType ==SFGNode::GROUPBY_TYPE)
			{
				if (nCid<0 || nCid>=(int)vGpName.size())
					continue;

				hsii=m_hmFieldNameId.find(vGpName[nCid].first);
				if (hsii==m_hmFieldNameId.end())
					continue;
				pProfile=m_vProfiles[hsii->second];
				if (pProfile==NULL)
					continue;
				vGpRes.resize(vGpRes.size()+1);
				vGpRes.back().first=hsii->second;

				const SGPFilter sgf=vFgn[i].sgpf;
				if (sgf.nCatlimit > 0 && sgf.nCatlimit < 8) //class group by limit
				{
					string scls = vGpName[nCid].second;
					if (scls.length() > 0)
					{
						int nCnt = 0;
						int nLimit = sgf.nCatlimit*2;
						size_t j = 0;
						for( ;j < scls.length() && nCnt < nLimit; ++j)
						{
							if ('0' <= scls[j] && scls[j] <= '9')
							{
								++nCnt;
							}
						}


						if (j != scls.length() && scls[scls.length()-1] == '-')
						{
							scls.resize(j);
							scls+='-';
						}
						else
							scls.resize(j);
						vGpName[nCid].second = scls;
					}
				}


				if (sgf.nPflId == -1 || m_vProfiles[sgf.nPflId] == NULL)
					GroupByOne(vSimpleIds, pProfile, vGpName[nCid].second, vGpRes.back());
				else
				{
					vector<int> vFilteredIds;
					CProfile<CAnyType>* pfl = (CProfile<CAnyType>*)m_vProfiles[sgf.nPflId];
					long long ll = 0;
					long long lmin = sgf.nMin;
					long long lmax = sgf.nMax;
					bool bNot = sgf.nNot;
					int nKeySize = (1<<pfl->m_nKeyPow);
					vFilteredIds.reserve(vSimpleIds.size());
					int clsLevel=0;
					bool bCat = (m_vFieldInfos[sgf.nPflId].nSpecialType == CAT_FIELD);
					if (bCat)
						clsLevel=GetClsLevel(lmin);

					for (size_t i=0;i<vSimpleIds.size();++i)
					{
						memcpy(&ll, pfl->GetFrstNumVal(vSimpleIds[i]), nKeySize);
						if (bCat)
						{
							if (bNot == (GetClassByLevel(clsLevel, ll) != (u64)lmin) )
								vFilteredIds.push_back(vSimpleIds[i]);
						}
						else if (bNot == (ll < lmin || ll > lmax) )
							vFilteredIds.push_back(vSimpleIds[i]);
					}
					GroupByOne(vFilteredIds, pProfile, vGpName[nCid].second, vGpRes.back());
				}
			}

		}
	}

	int id;
	for(i=0,j=0,k=0;i<vSimpleIds.size();++i)
	{
		id = vSimpleIds[i];
		while(vDocIds[j].nDocId!=id) //模块中不能对vSimpleIDs重排，不能增加元素否则会CORE DUMP
			++j;
		vDocIds[k]=vDocIds[j];
		++j;++k;
	}
	vDocIds.resize(k);
}


//智能化语法
void CSearcher::ChangePara(HSS &hssParseRes)
{

	if (hssParseRes.find(NC) != hssParseRes.end() && hssParseRes[NC] == "1")
	{
		return;
	}
	
	
	HSII j;
	vector<int> vCids;//必须转换查询方式的字段ID
	vector<int> vTids;//候选ID
	bool hasQueryClause = (hssParseRes.find(TQ) != hssParseRes.end());
	SFieldInfo sf;
	for (HSSI i = hssParseRes.begin(); i != hssParseRes.end(); ++i)
	{
		j = m_hmFieldNameId.find(i->first);
		if (j != m_hmFieldNameId.end())
		{
			sf = m_vFieldInfos[j->second];

			if (sf.chDataType == NUMBER	&& sf.bProfile && i->second.find('~')!=string::npos)
			{
				vCids.push_back(j->second);
				continue;
			}

			if (sf.chIndexType == FIELD_INDEX)
			{
				if (sf.chDataType == NUMBER	&& sf.bProfile && 
					hssParseRes.find(string("-") + i->first) == hssParseRes.end())
				{
					vTids.push_back(j->second);
				}
				else
					hasQueryClause = true;
			}
			else if (sf.chIndexType == TEXT_INDEX)
			{
				hasQueryClause = true;
			}
			else //must change
			{
				vCids.push_back(j->second);
			}
		}
		
	}

	if (hasQueryClause == false && !vTids.empty()) //优先考虑非参数字段
	{
		vector<int>::iterator i = vTids.begin();
		for (;i != vTids.end(); ++i)
		{
			if ( m_vFieldInfos[*i].nSpecialType != PARA_FILED)
			{
				vTids.erase(i);
				hasQueryClause = true;
				break;
			}
		}
		if (!hasQueryClause && !vTids.empty())
		{
			vTids.resize(vTids.size()-1);
		}
	}

	vCids.insert(vCids.end(), vTids.begin(),vTids.end());
	PSS pss;
	HSSI it;
	for (size_t i = 0; i != vCids.size(); ++i)
	{
		it = hssParseRes.find(m_vFieldInfos[vCids[i]].strFieldName);
		if (it != hssParseRes.end())
		{
			pss = *it;
			hssParseRes.erase(it);
			hssParseRes.insert(make_pair(string("-")+pss.first, pss.second));
			_COMMON_LOG(L_DEBUG, "%s replace with -%s", pss.first.c_str(), pss.first.c_str());
		}
	}
}

int CSearcher::Search(HSS &hssParseRes, string& strRes)
{
	vector<CFilter*> vF;
	vector<CTextQuery*> vTQ,vTQSuggest;
	vector<CQuery*> vFQ;
	vector<SResult> vResult;
	vector<PSS> vGPName;
	IAnalysisData* pad = NULL;
	CControl ctrl;
	//int  nRes=0;

	strRes.reserve(32*1024);


#ifndef _WIN32
	struct timeval tStartTime,tEndTime;
	::gettimeofday(&tStartTime, NULL);
	
#endif
	ModifyUrlPara(hssParseRes);
	CModule* pUseMod=GetQueryUseModule(hssParseRes);
	pUseMod->QueryRewrite(hssParseRes);

	GROUP_RESULT vGpRes;
	vector<string> vecRed;
	
	ChangePara(hssParseRes);
	if(Parse(hssParseRes,vF,vTQ,vFQ,vGPName,pad,ctrl,pUseMod)&&pad)
	{

		vector<SFGNode> vFgn;

		if (!pad->bAdvance)
			GetSuggestSearchFields(pad, vTQ, vTQSuggest);
		else
			vTQSuggest=vTQ;

		int wantCnt = pUseMod->GetReturnMaxDocNum();
		MatchDoc(vTQSuggest,vFQ,vResult,wantCnt,pUseMod);
        if(!m_bMatch || vTQSuggest.empty())
            FiltInvalidDoc(vResult);

		pUseMod->BeforeGroupBy(pad, vResult, vGPName,vGpRes);

		InitFiltAndGroupBySequence(vF,vGPName,vFgn);
		pUseMod->SetGroupByAndFilterSequence(pad,vFgn);
		FiltAndGroupBy(pUseMod,pad,vFgn,vResult,vF,vGPName,vGpRes);

		pUseMod->FillGroupByData(vGpRes);
		//pUseMod->FillGroupByData(vGpRes);

		int queryType=NOKEY_CLAUSE;
		if (!vTQ.empty())
		{
			CTextQuery* p=vTQ[0];
			if (p->m_andOr==CQuery::AND)
			{
				queryType=ADVANCE_CLAUSE;
				for (size_t i=0;i<vTQ.size();++i)
				{
					vector<string> v;
					vTQ[i]->GetHighLights(v);
					vecRed.insert(vecRed.end(),v.begin(),v.end());
				}
			}
			else
			{
				queryType=Q_CLAUSE;
				vTQ[0]->GetHighLights(vecRed);
			}
		}
		else //非文本搜索
		{
			if (!vFQ.empty())
			{
				pUseMod->ComputeWeight(pad, vResult);
			}
		}

		SortScore(ctrl,vResult,queryType,pUseMod,pad);
	}

	int nSpace = 0;
#ifndef _WIN32
	::gettimeofday(&tEndTime, NULL);
	nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
	nSpace += (tEndTime.tv_usec - tStartTime.tv_usec) / 1000;
	char buf[32];
	sprintf(buf,"%d",nSpace);
	if (pad)
		pad->m_hmUrlPara[COST_TIME] = buf;
#else
	pad->m_hmUrlPara[COST_TIME]="0";
#endif

	if(hssParseRes.find(FT)!=hssParseRes.end() &&
		atoi(hssParseRes[FT].c_str()) == MERGE_TYPE)
	{
		CModule* pDefMod = m_mods[DEFAULT_RANKING].pMod;
		pDefMod->ShowResult(pad, ctrl, vGpRes,vResult,vecRed,strRes);
	}
	else
		pUseMod->ShowResult(pad, ctrl, vGpRes,vResult,vecRed,strRes);

	if (pad->m_hmUrlPara[EC] == UTF8_FMT)
	{
		string s;
		s.resize(2*strRes.size()+1);
		GbkToUtf8((unsigned char*)strRes.c_str(), (unsigned char*)s.c_str());
		strRes = s.c_str();
		
	}
	
	UpdateStatInfo(vResult.size(),nSpace);

	DeletePtrVec(vF);
	DeletePtrVec(vTQ);
	DeletePtrVec(vFQ);
	delete pad;
	return atoi(hssParseRes[FT].c_str());

}

bool CSearcher::ParseQueryIntent(const char* parse_result, string& intentString)
{
	char *out;                                                         
	cJSON *json;
	vector<string> entityNames;
	map<string, bool> entityMap;
	map<string, bool>::iterator it;

    json = cJSON_Parse(parse_result);
    if (!json)
    {
		_COMMON_LOG(L_ERROR, "Parse query intent text string failed.");
        return false;
    } else {
        cJSON_bool isSucc = cJSON_HasObjectItem(json, "queryintent");
        if (!isSucc){
			_COMMON_LOG(L_ERROR, "query intent is parsing failed.");
            cJSON_Delete(json);
            return false;
        } else {
			cJSON* intent_json = cJSON_GetObjectItem(json, "queryintent");
            int int_json_array_size = cJSON_GetArraySize(intent_json);
			for (int i = 0; i < int_json_array_size; i++)
			{
				cJSON* item = cJSON_GetArrayItem(intent_json, i);
                cJSON* name_json = cJSON_GetObjectItem(item, "entityName");
                out = cJSON_Print(name_json);
				string keyword(out);
				it = entityMap.find(keyword);
				if (it != entityMap.end())
				{
					free(out);
					continue;
				} else {
					entityMap.insert(make_pair(keyword, true));
					entityNames.push_back(keyword);
                	free(out);
				}
			}

			for (int i = 0; i < entityNames.size(); i++)
			{
				intentString +=entityNames[i];
				if (i != entityNames.size()-1)
					intentString += " ";
			}
		}
		cJSON_Delete(json); 
	}

	return true;
}

bool CSearcher::HttpRequest(string queryword, char* queryResult)
{
	int sockfd;
	u_short port = 80;
	struct sockaddr_in dest;

	char message[1024];
	char response[4096];

	char *message_fmt = "GET /queryparser/?q=%s HTTP/1.0\r\n User-Agent: Mozilla/4.0 (compatible; MSIE5.01; Windows NT) \r\n Accept-Language: en-us \r\nAccept-Encoding: gzip, deflate \r\n Connection: Keep-Alive \r\n\r\n";

	if ((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
	{
		_COMMON_LOG(L_ERROR, "Fail to create socket handle.");
		return false;
	}

	bzero(&dest, sizeof(dest));
	dest.sin_family = AF_INET;
	dest.sin_port = htons(port);
	if (inet_aton("10.27.210.54", (struct in_addr *) &dest.sin_addr.s_addr) == 0)
	{
		_COMMON_LOG(L_ERROR, "Fail to socket inet_aton.");
		return false;
	}

	if (connect(sockfd, (struct sockaddr *) &dest, sizeof(dest)) < 0)
	{
		_COMMON_LOG(L_ERROR, "Fail to socket connect.");
		return false;
	}

	sprintf(message, message_fmt, queryword.c_str());
	//printf("Request:\n%s\n",message);

    /* send the request */
    int total = strlen(message);
	int bytes = 0;
    int sent = 0;
    do {
        bytes = write(sockfd,message+sent,total-sent);
        if (bytes < 0)
			_COMMON_LOG(L_DEBUG, "Fail to write socket .");
        if (bytes == 0)
            break;
        sent+=bytes;
    } while (sent < total);	

    /* receive the response */
    memset(response,0,sizeof(response));
    total = sizeof(response)-1;
    int received = 0;
    do {
        bytes = read(sockfd,response+received,total-received);
        if (bytes < 0)
			_COMMON_LOG(L_DEBUG, "Fail to read response.");
        if (bytes == 0)
            break;
        received+=bytes;
    } while (received < total);

	/* process response */
    //printf("Response:\n%s\n",response);
	memcpy((char*)queryResult, response, strlen(response) + 1);

	close(sockfd);

	return true;

}

int CSearcher::QueryParserIntentsRetrieval(string strQuery, string& keyResult)
{
	char queryResult[4096];
	HttpRequest(strQuery, queryResult);
	keyResult.erase(); 
	//cout << "queryResult:" << queryResult << endl;

	bool ret;
	if (strlen(queryResult) < 0)
	{
		_COMMON_LOG(L_ERROR, "query result failed to get.");
		return -1;

	}

	char* substr = strstr ( queryResult, "{" );
	if (!substr)
	{
		_COMMON_LOG(L_ERROR, "query result pre process failed.");
		return -1;
	}

	ret = ParseQueryIntent(substr, keyResult);
	if (!ret)
	{
		_COMMON_LOG(L_ERROR, "query intent parsing failed.");
		return -1;
	}
	return 0;
}

int CSearcher::SegmentWordsRetrieval(string& key, vector<string>& vFinalTerms, 
		vector<string>& vFinalUtf8Terms, vector<Term>& vTerms)
{
	char regularizedBuf[1024]={0};
	unsigned char GbkBuf[1024] = {0};

	memmove(regularizedBuf, key.c_str(), strlen(key.c_str())+1);
	Utf8ToGbk((const unsigned char*)regularizedBuf, GbkBuf);

	gs_cc.NormalizeString((char*)GbkBuf);
	/*
	gs_cc.Convert_t2s((char*)GbkBuf);
	gs_cc.ConvertDigitAlpha((char*)GbkBuf);
	*/

	string GbkStr = string((const char*)GbkBuf);
	GetTermInfoOpenApi2RPC(GbkStr, vFinalTerms, vTerms);

	/*Init the key before loop*/
	key = "";

	int count = 0;
	for (const auto &GbkPiece : vFinalTerms) 
	{
		char Utf8Buf[1024] = {0};
        GbkToUtf8((const unsigned char*)GbkPiece.c_str(), (unsigned char*)Utf8Buf);
		string Utf8Str((const char*)Utf8Buf);

		vFinalUtf8Terms.push_back(Utf8Str);
        key.append(Utf8Str);
        key.append(" ");
		count++;
	}

	return 0;
}

int CSearcher::DropOneWord(vector<string>& vFinalUtf8Terms, int index, string& key)
{
	if (index < 0 || index > vFinalUtf8Terms.size() - 1) return -1;
	int i = 0;
	for (const auto &Utf8Str: vFinalUtf8Terms)
	{
		if (i == index){
			i++;
			continue;
		}

        key.append(Utf8Str);
        key.append(" ");
		i++;
	}

	return 0;
}

void CSearcher::setShareHandle(CURL* curl_handle)
{
    static CURLSH* share_handle = NULL;
    if (!share_handle)
    {
        share_handle = curl_share_init();
        curl_share_setopt(share_handle, CURLSHOPT_SHARE, CURL_LOCK_DATA_DNS);
    }
    curl_easy_setopt(curl_handle, CURLOPT_SHARE, share_handle);
    curl_easy_setopt(curl_handle, CURLOPT_DNS_CACHE_TIMEOUT,60*10);
}   

size_t receive_data(const char* buffer, size_t size, size_t nmemb,string* data)
{
    int len = size * nmemb;
    data->append(buffer,len);
    return len;
}

bool CSearcher::ParseServiceJSON(const char* text, vector<string>& serviceAddrs)
{
	char *out;
	cJSON *json;
	json = cJSON_Parse(text);
    if (!json)
    {
        _SESSION_LOG(L_FATAL, __FILE__, __LINE__, "Parsing service discovery anwsering string is failed." );
        return false;
    } else {

 		int int_json_array_size = cJSON_GetArraySize(json);
		if (int_json_array_size < 0)
		{
			_SESSION_LOG(L_FATAL, __FILE__, __LINE__, "Parsing service discovery anwsering array is failed." );
			if (json) {
				cJSON_Delete(json);
			}
			return false;
		}

		for (int i = 0; i < int_json_array_size; i++)
		{                                                                                                     
			cJSON* item = cJSON_GetArrayItem(json, i);
			cJSON* serviceAddr = cJSON_GetObjectItem(item, "ServiceAddress");
			out = cJSON_Print(serviceAddr);
			serviceAddrs.push_back(out);
			free(out);
		}
	}

	if (json) {
		cJSON_Delete(json);
	}

	return true;

}

int CSearcher::HandleRequest2RPC(string& strQuery, string& strRes)
{
	long dice_roll = g_distribution(g_generator);  

	struct timeval tStartTime,tEndTime;
	::gettimeofday(&tStartTime, NULL);
	unsigned long nSpace = 0;

	CXmlHttp xh;
	const char* end;
	const char* mid;
	int itemcount = 0;
	string tmpQuery;
	string strBackendServer;

	string serviceDiscoveryUrl ;

	ifstream discovery_config_file("./discovery_config.txt");
	getline(discovery_config_file, serviceDiscoveryUrl);
	boost::algorithm::trim(serviceDiscoveryUrl);

	//string serviceDiscoveryUrl = "http://10.23.244.4:8500/v1/catalog/service/searchserver-roughing";	

	//TBT Core dump on curl_easy_perform
	CURL *curl;
	CURLcode code;
	vector<string> vServers;
	vServers.reserve(10);

	clock_t now = std::clock();

	double elapsed_secs;
	elapsed_secs = double(now - s_last_update_ee_)/(CLOCKS_PER_SEC + 1);

	curl = curl_easy_init();  

	if (s_firsttime || elapsed_secs > 10)
	{
		s_firsttime = false;
		s_last_update_ee_ = std::clock();

		m_urldata="";

		if (curl)
		{
    	    setShareHandle(curl);
    	    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, receive_data);
    	    curl_easy_setopt(curl, CURLOPT_URL,(char*)serviceDiscoveryUrl.c_str());
    	    curl_easy_setopt(curl, CURLOPT_WRITEDATA,&m_urldata);
    	    curl_easy_setopt(curl, CURLOPT_TIMEOUT, 10);
    	    curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
    	    //curl_easy_setopt(curl, CURLOPT_HEADERDATA, fp);
    	    code = curl_easy_perform(curl);
    	    if (code != 0)
    	    {
    	        curl_easy_cleanup(curl);
    	        _SESSION_LOG(L_ERROR, "get docinfo fail");
    	        return -1;
    	    } 

		}
	}

	curl_easy_cleanup(curl);

	//_SESSION_LOG(L_NOTICE, "service discovery url: %s", m_urldata.c_str());

	ParseServiceJSON(m_urldata.c_str(), vServers);

	if (vServers.size() <= 0)
	{
		_SESSION_LOG(L_ERROR, "token: %ld, Get ES servers failed. Exit.", dice_roll);
		return -1;
	} else {
		_SESSION_LOG(L_NOTICE, "token: %ld, vServers.size(): %d", dice_roll, vServers.size());
	}

	strBackendServer = vServers[m_counter++ % vServers.size()];
	if (m_counter == ULLONG_MAX - 1)
		m_counter = 0;
	strBackendServer = strBackendServer.substr(1, strBackendServer.size() - 2);
	_SESSION_LOG(L_NOTICE, "token: %ld, Request Begin: Backend ES server: %s", 
			dice_roll, strBackendServer.c_str());

	::gettimeofday(&tEndTime, NULL);
	nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
	nSpace += (tEndTime.tv_usec - tStartTime.tv_usec)/1000.0 ;

	_SESSION_LOG(L_NOTICE, "token: %ld, Get Backend server cost %ld ms.", dice_roll, nSpace);

	end = strstr(strQuery.c_str(), " HTTP");
	mid = strstr(strQuery.c_str(), "?");
	if (end && mid && end>mid)
		strQuery=string(mid+1,end);

	HSS hssParse;
	SortType sortType;

	xh.ParseRequest(strQuery, hssParse);

	if(hssParse[EC] != GBK_FMT)
		hssParse[EC] = UTF8_FMT;

	if(hssParse["sort"] == "new")
		sortType = SortType::ST_TIME;
	else 
		sortType = SortType::ST_SIMILARITY;


	if (hssParse[EC] == UTF8_FMT)
	{
		//_SESSION_LOG(L_NOTICE, "token: %ld, Original: %s", dice_roll, hssParse[TQ].c_str());
		string strTemp;
		string first;
		for(HSSI hi=hssParse.begin();hi!=hssParse.end();++hi)
		{
			strTemp.resize(hi->second.size() + 1,0);
			first = hi->first.substr(0,2);
			if(strcmp(first.c_str(),"__") == 0)
				continue;
			Utf8ToGbk((const unsigned char*)hi->second.c_str(),(unsigned char*)strTemp.c_str());
			hi->second = strTemp.c_str();
		}
	}

	if(hssParse.find(TQ) != hssParse.end())
	{
		char buf[1024]={0};
		strncpy(buf,hssParse[TQ].c_str(),sizeof(buf)-1);
		gs_cc.Convert_t2s(buf);
		gs_cc.ConvertDigitAlpha(buf);
		hssParse[TQ] = buf;
	}

	vector<CFilter*> vF;
	vector<CTextQuery*> vTQ,vTQSuggest;
	vector<CQuery*> vFQ;
	vector<SResult> vResult;
	vector<PSS> vGPName;
	IAnalysisData* pad = NULL;
	CControl ctrl;
	strRes.reserve(32*1024);

	ClientContext context;
	vector<SearchResult> sre_vec;
	vector<SearchMatchElement> sme_vec;
	vector<SMatchElement> vSME;
	vector<Term> vQueryTerms;
	GROUP_RESULT vGpRes;

	sre_vec.reserve(1024);
	sme_vec.reserve(1024);
	vSME.reserve(1024);

	ModifyUrlPara(hssParse);
	CModule* pUseMod=GetQueryUseModule(hssParse);

	// Query Rectify 
	HSSI hssi = hssParse.find("modify");
	if(hssi == hssParse.end()) 
	{
		hssParse.insert(make_pair("modify", "0"));

	} else if (hssi != hssParse.end() && hssi->second == "1")
	{
		hssi->second = "0";
	}

	pUseMod->QueryRewrite(hssParse);

	vector<string> vecRed;
	ChangePara(hssParse);

	if (Parse(hssParse,vF,vTQ,vFQ,vGPName,pad,ctrl,pUseMod)&&pad)
	{
		vector<SFGNode> vFgn;
		if (!pad->bAdvance)
			GetSuggestSearchFields(pad, vTQ, vTQSuggest);
		else
			vTQSuggest=vTQ;

		int wantCnt = pUseMod->GetReturnMaxDocNum();
		itemcount = wantCnt;


		grpc::ChannelArguments ch_args;
		ch_args.SetMaxReceiveMessageSize(GRPC_DEFAULT_MAX_RECV_MESSAGE_LENGTH);

		// This is only for testing
		
		string requestType = "";
		string materialType = "";
		ifstream backend_config_file("./backend_config.txt");
		string config_line;
		getline(backend_config_file, config_line);
		boost::algorithm::trim(config_line);

		vector<string> config_strs;
		boost::split(config_strs,config_line,boost::is_any_of("\t "));

		string strBackendServerPort = config_strs[0];
		requestType = config_strs[1];
		materialType = config_strs[2];
		strBackendServer = "10.27.82.85";

		string serverPort = strBackendServer + ":" + strBackendServerPort;

		IndexClient indexclient(grpc::CreateCustomChannel(
						serverPort, grpc::InsecureChannelCredentials(), ch_args));

		RequestType rt;
		MaterialType mt = MaterialType::MT_VIDEO;
		if (requestType == "RT_YUANCHUANG")
			rt = RequestType::RT_YUANCHUANG;
		else if (requestType == "RT_CHEJIAHAO")
			rt = RequestType::RT_CHEJIAHAO;

		if (materialType == "MT_ARTICLE")
			mt = MaterialType::MT_ARTICLE;
		else if (materialType == "MT_VIDEO")
			mt = MaterialType::MT_VIDEO;

		string& gbkquery = hssParse[TQ];

		{
			vector<string> vFinalTerms;
			vector<string> vFinalUtf8Terms;
			vector<SearchMatchElement> sme_vec_tmp;
			vector<SearchResult> sre_vec_tmp;

			string key ;
			string qpkey ;
			key.reserve(1024);
			qpkey.reserve(1024);

			char buf[1024] = {0};

			GbkToUtf8((unsigned char*)gbkquery.c_str(), (unsigned char*)buf);

			key = string(buf);

			_SESSION_LOG(L_NOTICE, "token: %ld, Rectify Query: %s", dice_roll, key.c_str());

			// Don't segment
			sre_vec_tmp.clear();
			sme_vec_tmp.clear();

			QueryType qt = QueryType::QT_AND;


			// Segment words without dropping
			SegmentWordsRetrieval(key, vFinalTerms, vFinalUtf8Terms, vQueryTerms);
			_SESSION_LOG(L_NOTICE, "token: %ld, Segmented: %s", dice_roll, key.c_str());

			::gettimeofday(&tEndTime, NULL);
			nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
			nSpace += (tEndTime.tv_usec - tStartTime.tv_usec)/1000.0 ;
			_SESSION_LOG(L_NOTICE, "token: %ld, Segment words with %ldms.", dice_roll, nSpace);

			indexclient.GetItems(key, itemcount, rt , sre_vec_tmp, sme_vec_tmp, qt, mt, sortType, *this, dice_roll);
			sre_vec.insert(sre_vec.end(), sre_vec_tmp.begin(), sre_vec_tmp.end());
			sme_vec.insert(sme_vec.end(), sme_vec_tmp.begin(), sme_vec_tmp.end());

			::gettimeofday(&tEndTime, NULL);
			nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
			nSpace += (tEndTime.tv_usec - tStartTime.tv_usec)/1000.0 ;
			_COMMON_LOG(L_WARN, "token: %ld, AND RPC call cost %ldms.", dice_roll, nSpace);

			::gettimeofday(&tEndTime, NULL);
			nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
			nSpace += (tEndTime.tv_usec - tStartTime.tv_usec)/1000.0 ;
			_SESSION_LOG(L_NOTICE, "token: %ld, Segment without dropping RPC call cost %ldms.", dice_roll, nSpace);

			::gettimeofday(&tEndTime, NULL);
			nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
			nSpace += (tEndTime.tv_usec - tStartTime.tv_usec)/1000.0 ;
			_COMMON_LOG(L_NOTICE, "token: %ld, RPC call cost %ldms.", dice_roll, nSpace);
		}

		vector<long long> vPrimaryKeys;
		vector<int > vDocIds;
		for (int i = 0; i < sme_vec.size(); i++)
		{
			vector<string> vTmpStr;
			string docidstr = sme_vec[i].docid();
			vTmpStr = split(docidstr, "-");
			vPrimaryKeys.push_back(atoi(vTmpStr[1].c_str()));
			if (atoi(vTmpStr[1].c_str()) < 0)
				cout << "|" << vTmpStr[1].c_str() << endl;
		}

		int fieldId = PRIMARY_KEY_INDEX;  // biz id
		GetDocsByPkOpenApi(this, fieldId, vPrimaryKeys, vDocIds);

		for (int i=0; i < sre_vec.size(); i++)
		{
			SResult sre;
			if (vDocIds[i] < 0) continue;
			sre.nDocId = vDocIds[i];
			sre.nWeight = sre_vec[i].weight();
			//TBD: Current ES index didn't provice the score.
			sre.nScore = sre_vec[i].score();

			vResult.push_back(sre);
		}

		/*TBD: vResult may not the same with sme*/
		FiltInvalidDoc(vResult);

		for (int i=0; i < sme_vec.size(); i++)
		{
			SMatchElement sme;
			if (vDocIds[i] < 0) continue;
			sme.id = vDocIds[i];
			sme.matchType = sme_vec[i].matchtype();
			FieldOffs fieldOffs = sme_vec[i].fieldoffs();

			if (fieldOffs.fieldoff_size() == 0) {

				SFieldOff sfieldoff;
				sfieldoff.field = m_hmFieldNameId["content"];
				sfieldoff.off = 3000;
				sme.vFieldsOff.push_back(sfieldoff);

			} else {
				for (int j = 0; j < fieldOffs.fieldoff_size(); j++)
				{
					FieldOff fieldoff = fieldOffs.fieldoff(j);
					SFieldOff sfieldoff ;
					sfieldoff.off = fieldoff.off();

					FieldType ft = fieldoff.field();
					string fieldName= fieldtype_map_[ft];
					HSII hsii = m_hmFieldNameId.find(fieldName);
					if (hsii == m_hmFieldNameId.end()) continue;
					else {
						sfieldoff.field = hsii->second;
					}

					/*
					if (sfieldoff.field == 1)
					{
						cout << "WANING::::id:" << sme.id << ", off:" << sfieldoff.off << ", field:" << sfieldoff.field << endl;
					}*/

					sme.vFieldsOff.push_back(sfieldoff);
				}
			}

			FieldLengths fieldlengths = sme_vec[i].fieldlengths();

			if (fieldlengths.fieldlength_size() == 0) {

				sme.vFieldLen.push_back(5);

			} else {
				for (int j = 0; j < fieldlengths.fieldlength_size(); j++)
				{
					sme.vFieldLen.push_back(fieldlengths.fieldlength(j));
				}
			}

			sme.vTerms = vQueryTerms;
			TFs tfs = sme_vec[i].tfs();
			if (tfs.tf_size() == 0) {

				sme.vTf.push_back(1);

			} else {
				for (int j=0; j < tfs.tf_size(); j++)
				{
					sme.vTf.push_back(tfs.tf(j));
				}
			}

			IDFs idfs = sme_vec[i].idfs();
			if (idfs.idf_size() == 0) {
				sme.vIdf.push_back(2.0);
			} else {
				for (int j=0; j < idfs.idf_size(); j++)
					sme.vIdf.push_back(idfs.idf(j));
			}
			vSME.push_back(sme);
		}

		pUseMod->BeforeGroupBy(pad, vResult, vGPName,vGpRes);

		InitFiltAndGroupBySequence(vF,vGPName,vFgn);
		pUseMod->SetGroupByAndFilterSequence(pad,vFgn);
		FiltAndGroupBy(pUseMod,pad,vFgn,vResult,vF,vGPName,vGpRes);

		pUseMod->FillGroupByData(vGpRes);

		int queryType=NOKEY_CLAUSE;
		if (!vTQ.empty())
		{
			CTextQuery* p=vTQ[0];
			if (p->m_andOr==CQuery::AND)
			{
				queryType=ADVANCE_CLAUSE;
				for (size_t i=0;i<vTQ.size();++i)
				{
					vector<string> v;
					vTQ[i]->GetHighLights(v);
					vecRed.insert(vecRed.end(),v.begin(),v.end());
				}
			}
			else
			{
				queryType=Q_CLAUSE;
				vTQ[0]->GetHighLights(vecRed);
			}
			if (pUseMod&&pad&&(!pad->bAdvance || !pad->bAutoAd))
			{
				for (int i = 0; i < vSME.size(); i++)
					pUseMod->ComputeWeight(pad, vSME[i], vResult[i]);
			}
		}
		else //非文本搜索
		{
			if (!vFQ.empty())
			{
				for (int i = 0; i < vSME.size(); i++)
					pUseMod->ComputeWeight(pad, vSME[i], vResult[i]);
			}
		}
		SortScore(ctrl,vResult,queryType,pUseMod,pad);
	}

	if(hssParse.find(FT)!=hssParse.end() &&
		atoi(hssParse[FT].c_str()) == MERGE_TYPE)
	{
		CModule* pDefMod = m_mods[DEFAULT_RANKING].pMod;
		pDefMod->ShowResult(pad, ctrl, vGpRes,vResult,vecRed,strRes);
	}
	else
		pUseMod->ShowResult(pad, ctrl, vGpRes,vResult,vecRed,strRes);
	
	if (pad->m_hmUrlPara[EC] == UTF8_FMT)
	{
		string s;
		s.resize(2*strRes.size()+1);
		GbkToUtf8((unsigned char*)strRes.c_str(), (unsigned char*)s.c_str());
		strRes = s.c_str();
	}

	::gettimeofday(&tEndTime, NULL);
	nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
	nSpace += (tEndTime.tv_usec - tStartTime.tv_usec)/1000.0 ;

	_SESSION_LOG(L_NOTICE, "token: %ld, Request End: HandleRequest2RPC cost %ld ms.", dice_roll, nSpace);

	UpdateStatInfo(vResult.size(),nSpace);

	::gettimeofday(&tEndTime, NULL);

	DeletePtrVec(vF);
	DeletePtrVec(vTQ);
	DeletePtrVec(vFQ);
	delete pad;
	return 0;
}

int CSearcher::HandleRequest(string& strQuery, string& strRes)
{
	CXmlHttp xh;
	//strQuery = xh.URLDecode(strQuery.c_str());
	const char* end;
	const char* mid;
	end = strstr(strQuery.c_str(), " HTTP");
	mid = strstr(strQuery.c_str(), "?");
	if (end && mid && end>mid)
		strQuery=string(mid+1,end);
	HSS hssParse;
	int ret;

	xh.ParseRequest(strQuery,hssParse);

	if(hssParse[EC] != GBK_FMT)
		hssParse[EC] = UTF8_FMT;
	if (hssParse[EC] == UTF8_FMT)
	{
		string strTemp;
		string first;
		for(HSSI hi=hssParse.begin();hi!=hssParse.end();++hi)
		{
			strTemp.resize(hi->second.size() + 1,0);
			first = hi->first.substr(0,2);
			if(strcmp(first.c_str(),"__") == 0)
				continue;
			Utf8ToGbk((const unsigned char*)hi->second.c_str(),(unsigned char*)strTemp.c_str());
			hi->second = strTemp.c_str();
		}
	}
	
	if(hssParse.find(TQ) != hssParse.end())
	{
		char buf[1024]={0};
		strncpy(buf,hssParse[TQ].c_str(),sizeof(buf)-1);
		gs_cc.Convert_t2s(buf);
		gs_cc.ConvertDigitAlpha(buf);
		hssParse[TQ] = buf;
	}

	
	if (hssParse.find(INDEX_ADD)!=hssParse.end() ||
		hssParse.find(INDEX_MODIFY)!=hssParse.end() ||
		hssParse.find(INDEX_DEL)!=hssParse.end() ||
		hssParse.find(INDEX_OPT)!=hssParse.end() ||
		hssParse.find(INDEX_RECOVER)!=hssParse.end())
	{
		_COMMON_LOG(L_DEBUG,"inc_num:%s",hssParse[INC_NUM].c_str());
		char buf[10240]={0};
		for(HSSI hi=hssParse.begin();hi!=hssParse.end();++hi)
		{
			strncpy(buf,hi->second.c_str(),sizeof(buf)-1);
			gs_cc.Convert_t2s(buf);
			gs_cc.ConvertDigitAlpha(buf);
			hi->second = buf;
		}
#ifndef _WIN32
		pthread_rwlock_rdlock(&m_rwlock);
#endif
		ret = UpdateDocInfo(hssParse,strRes);
#ifndef _WIN32
		pthread_rwlock_unlock(&m_rwlock);
#endif
		strRes+="<result>";
		strRes+=g_updateInfo[ret];
		strRes+="</result>";
		return XML_TYPE;
	}
	else if (hssParse.find(RELOAD_MODULE)!=hssParse.end())
	{
		ret = ReloadModules(hssParse[RELOAD_MODULE].c_str());
		if (ret != 0 )
		{
			_COMMON_LOG(L_ERROR, "reload module failed, mod name: %s", RELOAD_MODULE);
		}
		strRes+="<result>";
		strRes+=g_reloadInfo[ret];
		strRes+="</result>";
		_COMMON_LOG(L_NOTICE, "reload module %s info: %s", hssParse[RELOAD_MODULE].c_str(), g_reloadInfo[ret]);
		return XML_TYPE;
	}
	else if (hssParse.find(SHOW_MODULE)!=hssParse.end())
	{
		ShowModuleInfo(hssParse,strRes);
		return XML_TYPE;
	}
	else if (hssParse.find(SHOW_INFO)!=hssParse.end())
	{
		 ShowStatInfo(strRes);
		 return HTML_TYPE;
	}
	else if (hssParse.find(SHOW_CONF)!=hssParse.end())
	{
		ShowMainConf(strRes);
		return HTML_TYPE;
	}
	else if (hssParse.find(MODIFY_VCONF)!=hssParse.end())
	{
		ModifyVConf(hssParse, strRes);
		return HTML_TYPE;
	}
	else if (hssParse.find(SET_LOG_LEVEL)!=hssParse.end())
	{
		const char* p = "error";
		char c = hssParse[SET_LOG_LEVEL][0] -'0';
		if ( (size_t)c >=0 && (size_t)c < sizeof(g_log_level)/sizeof(g_log_level[0]))
		{
			m_slog.set_level(c);
			p = "ok";
		}
		strRes+="<result>";
		strRes+=p;
		strRes+="</result>";
		return XML_TYPE;
	}
	else
	{

#ifndef _WIN32
		struct timeval tStartTime,tEndTime;
		::gettimeofday(&tStartTime, NULL);
		if(hssParse.find(NLOG) == hssParse.end())
			m_slog.write_log(L_NOTICE, __FILE__, __LINE__, "query = %s ", strQuery.c_str());
		pthread_rwlock_rdlock(&m_rwlock);
#endif
		ret=Search(hssParse,strRes);

#ifndef _WIN32
		pthread_rwlock_unlock(&m_rwlock);
		::gettimeofday(&tEndTime, NULL);
		int nSpace = (tEndTime.tv_sec - tStartTime.tv_sec) * 1000;
		nSpace += (tEndTime.tv_usec - tStartTime.tv_usec) / 1000;
		if(hssParse.find(NLOG) == hssParse.end())
			m_slog.write_log(L_NOTICE, __FILE__, __LINE__, "HandleRequest: cost = %d ms", nSpace);
		m_slog.session_mark();
#endif
		return ret;
	}
}

int CSearcher::ShowModuleInfo(HSS &hssParse, string& strRes)
{
#ifndef _WIN32
	pthread_rwlock_rdlock(&m_rwlock);
#endif
	char buf[1024];
	strRes+="<result>";
	time_t tm = (time_t)(m_statInfo.nStartStamp);

	sprintf(buf, "<module name=\"searcher\" full_tm=\"%d\" inc_num=\"%d\" static_doc_cnt=\"%d\" total_doc_cnt=\"%d\" real_doc_cnt=\"%d\" sys_start_time=\"%ld\"></module>",
		m_timestamp, GetIncNum(),GetStaticDocCnt(),GetNewDocId(),GetNewDocId() - m_delMark.GetTrueBitNum(),tm);
	strRes += buf;
	for (MOD_MAP::iterator i = m_mods.begin(); i != m_mods.end(); ++i)
	{
		sprintf(buf,"<module name=\"%s\" full_tm=\"%d\" inc_num=\"0\" static_doc_cnt=\"0\" total_doc_cnt=\"0\" sys_start_time=\"%ld\"></module>",
			(i->first).c_str(), i->second.tm, tm);
		strRes += buf;
	}

	strRes += "</result>";

#ifndef _WIN32
	pthread_rwlock_unlock(&m_rwlock);
#endif
	return 0;
}


int CSearcher::UpdateDocInfo(HSS &hssParse, string& strRes)
{

	int ret=0;
	if (hssParse.find(INDEX_ADD)!=hssParse.end())
	{
		if (!GetIncStatus())
		{
			return INC_FROZEN;
		}

#ifndef _WIN32
		pthread_mutex_lock(&m_mutex);
#endif
		ret=AddDoc(hssParse);
#ifndef _WIN32
		pthread_mutex_unlock(&m_mutex);
#endif
	}
	else if (hssParse.find(INDEX_MODIFY)!=hssParse.end())
	{
	
#ifndef _WIN32
		pthread_mutex_lock(&m_mutex);
#endif
		ret=ModifyDoc(hssParse);
#ifndef _WIN32
		pthread_mutex_unlock(&m_mutex);
#endif
	}
	else if (hssParse.find(INDEX_DEL)!=hssParse.end())
	{
		
#ifndef _WIN32
		pthread_mutex_lock(&m_mutex);
#endif
		ret=ChangeDocMark(hssParse, true);
#ifndef _WIN32
		pthread_mutex_unlock(&m_mutex);
#endif
	}
	else if (hssParse.find(INDEX_RECOVER)!=hssParse.end())
	{

#ifndef _WIN32
		pthread_mutex_lock(&m_mutex);
#endif
		ret=ChangeDocMark(hssParse, false);
#ifndef _WIN32
		pthread_mutex_unlock(&m_mutex);
#endif
	}
	else if (hssParse.find(INDEX_OPT)!=hssParse.end())
	{

#ifndef _WIN32
		pthread_mutex_lock(&m_mutex);
#endif
		ret=OptmizeIndex();
#ifndef _WIN32
		pthread_mutex_unlock(&m_mutex);
#endif
	}
	return ret;

}
int CSearcher::OptmizeIndex()
{
	if(!Sync(GetIncNum()))
	{
			SetIncFail();
			return SYNC_ERROR;
	}

	int maxId = GetNewDocId() - 1;
	vector<int> vecDocMap(maxId+1);
	
	int j = 0;
	for (int i = 0; i <= maxId; ++i)
	{
		if (m_delMark.TestBit(i))
			vecDocMap[i] = -1;
		else
			vecDocMap[i] = j++;
	}

	int icnt = GetNewDocId() - GetStaticDocCnt();
	int totalCnt = j;
	if (totalCnt == 0 || icnt < 1)
	{
		return NOT_AFFECTED;
	}
	

	string strPre=string("opt_"INDEX);
	string str;

#ifndef WIN32
	system("rm -r opt_"INDEX);
	if(system("mkdir -p opt_"INDEX)!=0)
		return OTHER_ERROR;
#endif

#define SAMECLAUSES(strPre)  (strPre+INDEX_DIC).c_str(),(strPre+INDEX_IDX).c_str(),(strPre+INDEX_IVT).c_str()

	for (size_t i=0;i<m_vFieldIndexes.size();++i)
	{
		if (m_vFieldIndexes[i]!=NULL)
		{
			str = strPre+m_vFieldInfos[i].strFieldName;
			if(!((CImplIndex<int,int>*)(m_vFieldIndexes[i]))->MergeIndex(vecDocMap, maxId, SAMECLAUSES(str)))
				return INDEX_ADD_ERROR;
		}
	}

	for (size_t i=0;i<m_vTextIndexes.size();++i)
	{
		if (m_vTextIndexes[i]!=NULL)
		{
			str = strPre+m_vFieldInfos[i].strFieldName;

			if(!((CImplIndex<string,SIvtNode>*)(m_vTextIndexes[i]))->MergeIndex(vecDocMap, maxId, SAMECLAUSES(str)))
				return INDEX_ADD_ERROR;
		}
	}

	for (size_t i=0;i<m_vProfiles.size();++i)
	{
		if (m_vProfiles[i]!=NULL)
		{
			str = strPre + m_vFieldInfos[i].strFieldName;
			if(!((CProfile<CAnyType>*)(m_vProfiles[i]))->MergeProfile((str+PROFILE_IDX).c_str(), (str+PROFILE_DAT).c_str(),		
				vecDocMap, GetStaticDocCnt(),icnt ))
				return PROFILE_ADD_ERROR;
														
		}
	}
	if(!m_detail.MergeDetail((strPre+DETAIL_IDX).c_str(),(strPre+DETAIL_DAT).c_str(),maxId,vecDocMap,m_bMem))
		return DETAIL_ADD_ERROR;
	
	vector<char> vDelMark;
	vDelMark.resize(m_delMark.GetBitCount()/8);
	if(!WriteStruct((strPre+DEL_MARK).c_str(),vDelMark, false))
		return OTHER_ERROR;


	vector<uint> vmark;
	vmark.resize(1024);
	memcpy(&vmark[0], m_mapDocMark.GetPtr(), 16*sizeof(uint));
	vmark[0]=totalCnt;
	vmark[1]=totalCnt;
	vmark[3]=totalCnt;
	if(!WriteStruct((strPre+DOC_MARK).c_str(),vmark, false))
		return OTHER_ERROR;

#ifndef WIN32
	if(system("cp "INDEX"/"CONF_FILE" opt_"INDEX"/"CONF_FILE)!=0||
		system("cp "INDEX"/"FULL_TM" opt_"INDEX"/"FULL_TM)!=0||
		system("touch opt_"INDEX"_success")!=0)
		return OTHER_ERROR;
#endif
	return OK;

}



bool CSearcher::Dispose()
{
	if(!Sync(GetIncNum()))
		SetIncFail();
	for (size_t i=0;i<m_vTextIndexes.size();++i)
	{
		if (m_vTextIndexes[i])
		{
			m_vTextIndexes[i]->Dispose();
			delete m_vTextIndexes[i];
		}

	}
	for (size_t i=0;i<m_vFieldIndexes.size();++i)
	{
		if (m_vFieldIndexes[i])
		{
			m_vFieldIndexes[i]->Dispose();
			delete m_vFieldIndexes[i];
		}
	
	}
	m_detail.Dispose();
//	DeletePtrVec(m_vProfiles);
	COMMON_FALSE_RETURN(!CInvertReader::GlobleDispose());
	m_slog.write_log(L_NOTICE, __FILE__, __LINE__, "searcher exit");
	m_slog.session_mark();
	m_slog.close();

	curl_global_cleanup();
	return true;
}


bool CSearcher::Init()
{
	if(!m_slog.init(LOG_DIR))
	{
		fprintf(stderr, "log system init fail\n");
		return false;
	}
	write_log_open_version(&m_slog, true, L_NOTICE, __FILE__, __LINE__, "searcher start");
	m_nPK=-1;

	COMMON_FALSE_RETURN(!CInvertReader::GlobleInit(DB_HOME));
	CConfig cfg(INDEX"/"CONF_FILE);
	COMMON_FALSE_RETURN(!cfg.GetFieldInfo(m_vFieldInfos,m_hmFieldNameId));
	COMMON_FALSE_RETURN(!g_analyzer.Init(SEGMENT_RPATH));

	string sTbPre = string(INDEX)+string("/");
	int sz;


	COMMON_FALSE_RETURN(NULL==m_mapDocMark.OpenMapPtr((string(sTbPre)+DOC_MARK).c_str(),false,0,sz,true));
	COMMON_FALSE_RETURN(!ReadBaseTimeStamp((string(sTbPre)+FULL_TM).c_str(),m_timestamp));
	COMMON_FALSE_RETURN(!m_delMark.OpenBitMap((sTbPre+DEL_MARK).c_str(), MAX_MARK_COUNT));

	BackUpIncInfo();
	for (size_t i=0;i<m_vFieldInfos.size();++i)
	{	
		SFieldInfo &fi=m_vFieldInfos[i];
		m_vFieldIndexes.push_back(NULL);
		m_vTextIndexes.push_back(NULL);
		m_vProfiles.push_back(NULL);

		string strPre=sTbPre+fi.strFieldName;
#define SAMECLAUSE  (strPre+INDEX_DIC).c_str(),(strPre+INDEX_IDX).c_str(),(strPre+INDEX_IVT).c_str(),DB_IDX_PAGESIZE,fi,GetStaticDocCnt()
		if (fi.chIndexType==FIELD_INDEX)
		{
			if (fi.chDataType==STRING)
			{
				m_vFieldIndexes.back()=new CImplIndex<string,int>(fi.bUseHash);
				COMMON_FALSE_RETURN(!((CImplIndex<string ,int>*)(m_vFieldIndexes.back()))->LoadIndex(SAMECLAUSE));
			}
			else
			{
				switch (fi.nKeyPow)
				{
				case 0: 
					m_vFieldIndexes.back()=new CImplIndex<char,int>(fi.bUseHash);
					COMMON_FALSE_RETURN(!((CImplIndex<char,int>*)(m_vFieldIndexes.back()))->LoadIndex(SAMECLAUSE));
					break;
				case 1: 
					m_vFieldIndexes.back()=new CImplIndex<short,int>(fi.bUseHash);
					COMMON_FALSE_RETURN(!((CImplIndex<short,int>*)(m_vFieldIndexes.back()))->LoadIndex(SAMECLAUSE));
					break;
				case 2:
					m_vFieldIndexes.back()=new CImplIndex<int,int>(fi.bUseHash);
					COMMON_FALSE_RETURN(!((CImplIndex<int,int>*)(m_vFieldIndexes.back()))->LoadIndex(SAMECLAUSE));
					break;
				case 3: 
					m_vFieldIndexes.back()=new CImplIndex<long long,int>(fi.bUseHash);
					COMMON_FALSE_RETURN(!((CImplIndex<long long ,int>*)(m_vFieldIndexes.back()))->LoadIndex(SAMECLAUSE));
					break;
				default:
					m_vFieldIndexes.back()=new CImplIndex<string,int>(fi.bUseHash);
					COMMON_FALSE_RETURN(!((CImplIndex<string ,int>*)(m_vFieldIndexes.back()))->LoadIndex(SAMECLAUSE));
					break;
				}
			}
		}

		if (fi.chIndexType==TEXT_INDEX)
		{
			m_vTextIndexes.back()=new CImplIndex<string,SIvtNode>(fi.bUseHash);
			COMMON_FALSE_RETURN(!((CImplIndex<string,SIvtNode>*)(m_vTextIndexes.back()))->LoadIndex(SAMECLAUSE));
		}

		if (fi.bProfile)
		{
			CProfile<char>* p;
			CProfile<short>* p1;
			CProfile<int>* p2;
			CProfile<long long>* p3;
			switch (fi.nKeyPow)
			{
			case 0: 
				p=new CProfile<char>();
				COMMON_FALSE_RETURN(!p->LoadProfile((strPre+PROFILE_IDX).c_str(), (strPre+PROFILE_DAT).c_str(), 
					&m_delMark, fi,GetStaticDocCnt(),GetNewDocId()));
				m_vProfiles.back()=p;
				break;
			case 1:
				p1=new CProfile<short>();
				COMMON_FALSE_RETURN(!p1->LoadProfile((strPre+PROFILE_IDX).c_str(), (strPre+PROFILE_DAT).c_str(), 
					&m_delMark, fi,GetStaticDocCnt(),GetNewDocId()));
				m_vProfiles.back()=p1;
				break;
			case 2:
				p2=new CProfile<int>();
				COMMON_FALSE_RETURN(!p2->LoadProfile((strPre+PROFILE_IDX).c_str(), (strPre+PROFILE_DAT).c_str(), 
					&m_delMark,fi,GetStaticDocCnt(),GetNewDocId()));
				m_vProfiles.back()=p2;
				break;
			case 3:
				p3=new CProfile<long long>();
				COMMON_FALSE_RETURN(!p3->LoadProfile((strPre+PROFILE_IDX).c_str(), (strPre+PROFILE_DAT).c_str(), 
					&m_delMark,fi,GetStaticDocCnt(),GetNewDocId()));
				m_vProfiles.back()=p3;
				break;
			default://string
				break;
			}
			if (fi.bPk)
			{
				m_nPK=i;
			}
		}
		if (fi.bShow)
		{
			m_vDtlFldIds.push_back(i);
		}
	}
	
	COMMON_FALSE_RETURN(!m_incFrequency.init("inc_sync_frequency", INC_FREQUENCY, 1, 100000, g_var_set));
	COMMON_FALSE_RETURN(!m_impFieldMaxRet.init("imp_field_max_get", MAX_IMP_FIELD_RET_CNT, 1, 2000000, g_var_set));
	COMMON_FALSE_RETURN(!m_overFieldMaxRet.init("over_field_max_get", MAX_OVER_FIELD_MATCH, 1, 2000000, g_var_set));
	COMMON_FALSE_RETURN(!m_scatterLimit.init("scatter_limit", MAX_SCATTER_LIMIT, 1, 5000, g_var_set));
	COMMON_FALSE_RETURN(!m_testVarConf.init("test_conf_opt", 12345, 1, 100000000, g_var_set));

	COMMON_FALSE_RETURN(!var_store_conf(BAK_VAR_CONF_FILE, g_var_set));
	if(!var_load_conf(VAR_CONF_FILE, g_var_set))
	{
		_COMMON_LOG(L_NOTICE, "load last var_conf error,use default!");
		COMMON_FALSE_RETURN(!var_store_conf(VAR_CONF_FILE, g_var_set));
	}

    m_bMem=0;
    m_bMatch=0;
	if(!ParseConf(SEARCH_DATA_CONF))
	{
		_COMMON_LOG(L_NOTICE, "load search_data_conf error,use um default!");
	}
	COMMON_FALSE_RETURN(!m_detail.LoadDetail((sTbPre+DETAIL_IDX).c_str(),(sTbPre+DETAIL_DAT).c_str(),DB_DTL_PAGESIZE,m_bMem));
	COMMON_FALSE_RETURN(!InitCodeConverter());

#ifndef _WIN32
	COMMON_FALSE_RETURN(pthread_mutex_init(&m_mutex, NULL));
	COMMON_FALSE_RETURN(pthread_rwlock_init(&m_rwlock, NULL)!=0);
	COMMON_FALSE_RETURN(ReloadModules(DEFAULT_RANKING)!=0);
	SearchModules();
#else
	COMMON_FALSE_RETURN(ReloadModules(DEFAULT_RANKING)!=0);
	COMMON_FALSE_RETURN(ReloadModules(KEYRANKING_DIR)!=0);
	COMMON_FALSE_RETURN(ReloadModules(FUZZYRANKING_DIR)!=0);
	//COMMON_FALSE_RETURN(ReloadModules(LISTRANKING_DIR)!=0);
	COMMON_FALSE_RETURN(ReloadModules(MIX_RECO_DIR)!=0);
	//FALSE_RETURN(ReloadModules(EG4KEYRANKING_DIR)!=0);
#endif
	InitStatInfo();

	curl_global_init(CURL_GLOBAL_ALL);

	m_counter = 0;

	fieldtype_map_[FieldType::FT_TITLE] = "title";
	fieldtype_map_[FieldType::FT_STITLE] = "stitle";
	fieldtype_map_[FieldType::FT_AUTHOR] = "author";
	fieldtype_map_[FieldType::FT_DESCRIPTION] = "description";
	fieldtype_map_[FieldType::FT_CONTENT] = "content";

	return true;
}

void CSearcher::GetTermWeight(vector<string>& vKeys,vector<Term>& vTerms)
{
    CFuzzyModule* pFuzMod = NULL;
    MOD_MAP::iterator it;
    if((it = m_mods.find(FUZZYRANKING_DIR)) != m_mods.end())
        pFuzMod = (CFuzzyModule*)(it->second.pMod);
    else
        return;
    pFuzMod->ComputeTermScore(vKeys,vTerms);
}

int CSearcher::SearchModules()
{
#ifndef _WIN32

	string str = MODULES_DIR"/";

	DIR *dp;
	struct dirent *entry;
	//struct stat statbuf;
	if((dp = opendir(str.c_str())) == NULL)
	{
		//fprintf(stderr,"cannot open directory: %s\n", str.c_str());
		_COMMON_LOG(L_ERROR, "cannot open directory: %s", str.c_str());
		return -1;
	}
	while((entry = readdir(dp)) != NULL)
	{
		//lstat(entry->d_name,&statbuf);
		//if(S_ISDIR(statbuf.st_mode))
		//{

			if(strcmp(".",entry->d_name) == 0 ||
				strcmp("..",entry->d_name) == 0)
				continue;
			_COMMON_LOG(L_ERROR, "entry->d_name:%s",entry->d_name );
			if(ReloadModules(entry->d_name)!=0)
				//fprintf(stderr,"file:%s, line:%d, dir:%s,info:%s",__FILE__,__LINE__,entry->d_name,strerror(errno));
				_COMMON_LOG(L_WARN, "dir:%s,info:%s",entry->d_name,strerror(errno));

		//}
	}
	closedir(dp);
#endif

	return 0;
}

bool CSearcher::GetDocDataInfo(int nDocId, string sFieldName, long& lFieldValue){
    if (nDocId>=GetNewDocId())
    {
		_COMMON_LOG(L_ERROR, "error info: %s\n", strerror(errno));
        return false;
    }

    int profile_size = m_vProfiles.size();
	int iFieldIdx = -1;
	for (int i = 0; i < profile_size; i++)
	{
		if (m_vFieldInfos[i].strFieldName == sFieldName)
		{
			iFieldIdx = i;
			break;
		}
	}

	if (iFieldIdx == -1)
	{
		_COMMON_LOG(L_ERROR, "error info: %s\n", strerror(errno));
        return false;
	}

    CProfile<CAnyType>* pfl;
	pfl = (CProfile<CAnyType>*)(m_vProfiles[iFieldIdx]);

	if (!pfl) {
		_COMMON_LOG(L_ERROR, "error info: %s\n", strerror(errno));
		return false;
	}

    void* pVal = pfl->GetSingleNumVal(nDocId);                                                                   
    m_vFieldInfos[iFieldIdx].nKeyPow == 3?                                                                                 
    		lFieldValue = *(long long*)pVal:                                                                                  
    		lFieldValue = *(int*)pVal;

	return true;

}

int CSearcher::ReloadModules(const char* mod)
{
#ifndef _WIN32
	pthread_rwlock_wrlock(&m_rwlock);
#endif

	MOD_MAP::iterator i = m_mods.find(mod);
	//CModule* ptemp = NULL;
	bool bDefault = false;
	if (strcmp(mod, DEFAULT_RANKING) == 0)//default
	{
		bDefault = true;
	}

	//void* oldSoHandle=NULL;

	if (i != m_mods.end())
	{
		if (bDefault)
			delete i->second.pMod;
		else
		{
#ifndef _WIN32
			if (i->second.hDll)
				dlclose(i->second.hDll);
#else
			delete i->second.pMod;
#endif
		}
		m_mods.erase(i);
	}

	//raise(SIGINT);
	CModule* pm;
	int tm = 0;
	void *soHandle = NULL;
	string str = MODULES_DIR"/";
	str += mod;
	if (bDefault)//default
	{
		pm = new CRanking();
	}
	else //load other module
	{

#ifdef _WIN32
		if (strcmp(mod, KEYRANKING_DIR) == 0)
		{
			pm = new CKeyRanking();
		}
		else if (strcmp(mod, LISTRANKING_DIR) == 0)
		{
			//pm = new CListRanking();
		}
		else if (strcmp(mod, MIX_RECO_DIR) == 0)
		{
			pm = new CMixReco();
		}
// 		else if (strcmp(mod, EG4KEYRANKING_DIR) == 0)
// 		{
// 			pm = new CEgKeyRanking();
// 		}
		else
			return MODULE_NOT_SUPPORT;
#else

		// 加载动态库
		const char* path = (str+"/"+mod+".so").c_str();
		soHandle = dlopen(path, RTLD_LAZY);
		if (soHandle == NULL)
		{
			pthread_rwlock_unlock(&m_rwlock);
			_COMMON_LOG(L_ERROR, "mod %s : %s , path : %s", mod, dlerror(), path);
			return MODULE_INIT_FAIL;
		}

		// 获取插件实现
		pm = (CModule*)dlsym(soHandle, mod);
		printf("%p: pm addr\n",pm);
		if (pm == NULL)
		{
			dlclose(soHandle);
			pthread_rwlock_unlock(&m_rwlock);
			_COMMON_LOG(L_ERROR, "mod %s : %s ", mod, dlerror());
			return MODULE_INIT_FAIL;
		}
#endif
	}
		
	int ret = 0;	
	if(!bDefault && !ReadBaseTimeStamp((str+"/"FULL_TM).c_str(), tm))
	{
		_COMMON_LOG(L_ERROR, "error: mod %s lost time_stamp", mod);
		ret = MODULE_MISS_TM;
	}

	SSearchDataInfo sdi;
	sdi.vFieldInfo=m_vFieldInfos;
	sdi.vProfiles=m_vProfiles;
	sdi.hmFieldNameId=m_hmFieldNameId;
	sdi.mapMod=&m_mods;
	sdi.pSearcher=this;
	sdi.pLogger=&m_slog;
	sdi.sgvf.funcFrstInt=GetSingleIntValOpenApi;
	sdi.sgvf.funcFrstInt64=GetLongLongValOpenApi;
	sdi.sgvf.funcFrstPtr=GetSingleNumValOpenApi;
	sdi.sgvf.funcValPtr=GetValOpenApi;
	sdi.sgvf.funcDocInfoPtr=GetDocDataOpenApi;
	sdi.sof.funcGpCLsPtr=GroupByClassOpenApi;
	sdi.sof.funcWriteLogPtr=write_log_open_version;
	sdi.sof.funcGetDocsByPkPtr=GetDocsByPkOpenApi;
	sdi.sof.funcScatterResult=ScatterResultOpenApi;
	sdi.sof.funcGetTermInfo=GetTermInfoOpenApi;
	sdi.sof.funcGetTermWeight=GetTermWeightOpenApi;
	sdi.sof.funcGetIdf=GetIdfOpenApi;

	if(!pm->Init(&sdi, str+"/"+mod+".conf"))
	{
		_COMMON_LOG(L_ERROR, "error: mod %s init fail", mod);
		ret = MODULE_INIT_FAIL;
	}
	
	if(ret!=0)
	{
		if (bDefault)
			delete pm;
		else
		{
#ifndef _WIN32
			if (soHandle)
				dlclose(soHandle);
#else
			delete pm;
#endif
		}

#ifndef _WIN32
		pthread_rwlock_unlock(&m_rwlock);
#endif
		return ret;
	}

	m_mods[mod].pMod = pm;
	m_mods[mod].tm = tm;
	m_mods[mod].hDll = soHandle;

#ifndef _WIN32
	pthread_rwlock_unlock(&m_rwlock);
#endif
	return 0;
}

void GetTermWeightOpenApi(void* pSearcher,vector<string>& vKeys,vector<Term>& vTerms)
{
    CSearcher* pSr=(CSearcher*)pSearcher;
    pSr->GetTermWeight(vKeys,vTerms);
}
void GetIdfOpenApi(void* pSearcher,map<string,float>& mTerms,string& type)
{
    CSearcher* pSr=(CSearcher*)pSearcher;
    pSr->GetTermIdf(mTerms,type);
}

void GetTermInfoOpenApi(string& key,vector<string>& vFinalTerms)
{
	if(key.empty())
		return;

	vFinalTerms.clear();
	vector<Term> vOrgTerms;
	//最大切分
	g_analyzer.Segment((char*)key.c_str(),key.size(),vOrgTerms, false, MM_SEG_FIELD);

	for(size_t i = 0;i < vOrgTerms.size();i++)
	{
		segment::Term& term = vOrgTerms[i];
		string str(key.c_str() + term.pos,term.len);
        if(!g_analyzer.IsStopWord(str) && !((term.len<=2)&&g_analyzer.IsInvalidChar(str.c_str(), term.len)))
			vFinalTerms.push_back(str);

	}
}

void CSearcher::GetTermInfoOpenApi2RPC(string& key,vector<string>& vFinalTerms, vector<Term>& vOrgTerms)
{
	if(key.empty())
		return;

	vFinalTerms.clear();
	//最大切分
	g_analyzer.Segment((char*)key.c_str(),key.size(),vOrgTerms, false, MM_SEG_FIELD);

	for(size_t i = 0;i < vOrgTerms.size();i++)
	{
		segment::Term& term = vOrgTerms[i];
		string str(key.c_str() + term.pos,term.len);
        if(!g_analyzer.IsStopWord(str) && !((term.len<=2)&&g_analyzer.IsInvalidChar(str.c_str(), term.len)))
			vFinalTerms.push_back(str);
	}
}

void GetDocDataOpenApi(int nDocId, vector<int>& vShowFieldIds, 
					   vector<char*>& vFieldDataPtr, 
					   vector<char>& vDataBuf, void* pSearcher)
{
	CSearcher* pSr=(CSearcher*)pSearcher;
	if (nDocId>=pSr->GetNewDocId())
	{
		write_log_open_version(&(pSr->m_slog), true, L_ERROR, __FILE__, __LINE__, "error info: %s\n", strerror(errno));
		return ;
	}
	CDetail& detail=pSr->m_detail;
	vector<int>& vDtlFldIds=pSr->m_vDtlFldIds;
	vector<SFieldInfo>& vFieldsInfo=pSr->m_vFieldInfos;
	vector<void*>& vProfiles=pSr->m_vProfiles;

	char* pzero=(char*)("\0");
	size_t i,j,step,fid;
	vFieldDataPtr.resize(vShowFieldIds.size());
	for (i=0;i<vFieldDataPtr.size();++i)
	{
		vFieldDataPtr[i]=pzero;
	}

	const char* pDocDetail;
	//const char* pBackDetail;
	SFetchInfo fi;
	pDocDetail=detail.GetData(nDocId,fi,pSr->m_bMem);
	
	if (!pDocDetail)
	{
		write_log_open_version(&(pSr->m_slog), true, L_ERROR, __FILE__, __LINE__, "error info: %s\n", strerror(errno));
		return ;
	}

	vDataBuf.clear();
	vDataBuf.reserve(detail.GetDocLen(nDocId)+256);

	vector<unsigned char> vConvBuf;


	char buf[128];
	time_t tp;
	struct tm* ptm;
	struct tm tm;
	CProfile<CAnyType>* pfl;

	i=0;
	for (j=0;j<vShowFieldIds.size();++j)
	{
		while(i!=vDtlFldIds.size()&&vDtlFldIds[i]!=vShowFieldIds[j])
		{
			pDocDetail+=strlen(pDocDetail)+1;
			++i;
		}
		if (i!=vDtlFldIds.size())
		{

			fid=vDtlFldIds[i];
			if (vFieldsInfo[fid].chDataType==NUMBER&&
				vFieldsInfo[fid].bProfile&&
				vFieldsInfo[fid].nKeyCnt)
			{
				pfl=(CProfile<CAnyType>*)(vProfiles[fid]);
				void* pVal=pfl->GetSingleNumVal(nDocId);
				if (vFieldsInfo[fid].nSpecialType == DATE_TIME_FIELD)
				{
					vFieldsInfo[fid].nKeyPow == 3?
						tp = *(long long*)pVal:
						tp = *(int*)pVal;
#ifdef _WIN32
					ptm = localtime(&tp);
#else
					ptm = localtime_r(&tp, &tm);
#endif
					if (ptm == NULL ||  tp == 0)
					{
						buf[0] = '\0';
					}
					else
						strftime(buf, sizeof(buf), DATE_FORMAT, ptm);
				}
				else 
				{
					switch(pfl->m_nKeyPow)
					{
					case 0:
						sprintf(buf, "%d",(int)(*(char*)pVal));
						break;
					case 1:
						sprintf(buf, "%d",(int)(*(short*)pVal));
						break;
					case 2:
						sprintf(buf, "%d",(int)(*(int*)pVal));
						break;
					case 3:
						sprintf(buf, "%lld",(long long)(*(long long*)pVal));
						break;
					}
				}
				step=strlen(buf);
				vDataBuf.resize(vDataBuf.size()+step+1);
				memcpy(&vDataBuf.back()-step,buf,step+1);
				vFieldDataPtr[j]=&vDataBuf.back()-step;
			}
			else
			{
				step=strlen(pDocDetail);
				int oldSize = vDataBuf.size();
				vDataBuf.resize(vDataBuf.size()+step+1);
				char* p = &vDataBuf.back()-step;
				memcpy(p,pDocDetail,step+1);
				RemoveIllegalChar(p);
				vDataBuf.resize(oldSize + strlen(p) + 1);
				vFieldDataPtr[j]=p;
			}
		}


	}
	detail.PutData(fi);

}

void GetDocsByPkOpenApi(void* pSearcher, int fid, vector<long long>& vPk, vector<int>& vDocIds)
{
	
	CSearcher* pSr=(CSearcher*)pSearcher;
	if (fid < 0 || fid >= (int)pSr->m_vFieldIndexes.size() || pSr->m_vFieldIndexes[fid] == NULL)
	{
		vDocIds.resize(vPk.size(), -1);
		return;
	}

	vDocIds.reserve(vPk.size());
	if (pSr->m_vFieldInfos[fid].nKeyPow == 3)
	{
		CFieldQuery<long long> fq;
		CImplIndex<long long,int>* pIndex = (CImplIndex<long long,int>*)(pSr->m_vFieldIndexes[fid]);
		fq.Prepare(pIndex, pSr->GetNewDocId()-1);
		for (size_t i=0;i<vPk.size();++i)
			vDocIds.push_back(fq.DoFieldQueryPeekOne(vPk[i]));
	}
	if (pSr->m_vFieldInfos[fid].nKeyPow == 2)
	{
		CFieldQuery<int> fq;
		CImplIndex<int,int>* pIndex = (CImplIndex<int,int>*)(pSr->m_vFieldIndexes[fid]);
		fq.Prepare(pIndex, pSr->GetNewDocId()-1);
		for (size_t i=0;i<vPk.size();++i)
			vDocIds.push_back(fq.DoFieldQueryPeekOne((int)vPk[i]));

	}
	else //未实现
	{
		vDocIds.resize(vPk.size(),-1);
	}
}





void CSearcher::ShowStatInfo(string& str)
{
	time_t tm;
	int t;
	//char buf[1024];
	str="查询总数:";
	str+=m_statInfo.nSrchCnt;
	str+="<br>无结果总数:";
	str+=m_statInfo.nNoResCnt;
	str+="<br>静态文档数:";
	str+=m_statInfo.nStaticDocCnt;
	str+="<br>总记录数：";
	str+=GetNewDocId();
	str+="<br>平均查询时间:";
	str+=(int)Mul(m_statInfo.nTotalTime, m_statInfo.nSrchCnt);
	str+="<br>系统启动时间:";
	tm=(time_t)(m_statInfo.nStartStamp);
	str+=ctime(&tm);
	str+="<br>全量数据时间:";
	tm=(time_t)(m_statInfo.nFullUpStamp);
	str+=ctime(&tm);
	str+="<br>最长query时间:";
	str+=m_statInfo.nMaxTime;
	str+="<br>日志级别:";
	str+=g_log_level[m_slog.get_level()];

	str+="<br><br>总响应时间统计";
	for (size_t i=0; i<sizeof(g_timeTitle)/sizeof(g_timeTitle[0]);++i)
	{
		str+="<br>";
		str+=g_timeTitle[i];
		str+=(int)Mul((u64)(m_statInfo.arrTotalSpan[i])*100, m_statInfo.nSrchCnt);
		str+="%";
	}

	if (m_statInfo.nSrchCnt>=100)
	{
		
		int arr[5]={0};
		for (int i=0;i<100;++i)
		{
			t=m_statInfo.arrRecentRes[i];
			if (t>=0)
			{
				if (t>100)
					t=100;
				arr[g_timeSpanRuler[t/10]]++;
			}
		}


		str+="<br><br>最近100次请求响应时间统计";
		for (size_t i=0; i<sizeof(g_timeTitle)/sizeof(g_timeTitle[0]);++i)
		{
			str+="<br>";
			str+=g_timeTitle[i];
			str+=arr[i];
			str+="%";
		}
	}
}

void CSearcher::ShowMainConf(string& str)
{
	str.reserve(1024*1024);
	str = "<table border=\"1\" width=\"100%%\">";
	str+="<tr>\
		<td>字段名称</td>\
		<td>数据类型</td>\
		<td>单值长度</td>\
		<td>值个数</td>\
		<td>索引类型</td>\
		<td>基准权重</td>\
		<td>汇总优化</td>\
		<td>建立属性</td>\
		<td>是否展示</td>\
		<td>特殊类型</td>\
		<td>是否主键</td>\
		</tr>";
	const char* YES_NO[]={"否","是"};
	const char* S_TYPE[]={"/","分类", "位域", "参数","日期","字切分","字符切分","同义索引","最大切分"};

	SFieldInfo* sf;

	for (size_t i=0;i<m_vFieldInfos.size();++i)
	{
		sf=&(m_vFieldInfos[i]);
		str+="<tr>";
		str+="<td>";
		str+=sf->strFieldName;
		str+="</td>";

		str+="<td>";
		str+=(sf->chDataType == NUMBER? "number":"string");
		str+="</td>";

		str+="<td>";
		if (sf->chDataType == NUMBER)
			str+=(1<<sf->nKeyPow);
		else
			str+="/";
		str+="</td>";

		str+="<td>";
		if (sf->nKeyCnt == 0)
			str+="可变";
		else
			str+=sf->nKeyCnt;
		str+="</td>";

		str+="<td>";
		str+=(sf->chIndexType == FIELD_INDEX? " 字段索引 ":
			(sf->chIndexType == TEXT_INDEX ? " 文本索引 ": "/") );
		str+="</td>";

		str+="<td>";
		str+=sf->nBaseWeight;
		str+="</td>";

		str+="<td>";
		str+=YES_NO[(bool)(sf->nGpOptimize)];
		str+="</td>";

		str+="<td>";
		str+=YES_NO[sf->bProfile];
		str+="</td>";

		str+="<td>";
		str+=YES_NO[sf->bShow];
		str+="</td>";

		str+="<td>";
		if (sf->nSpecialType >= INVALID_STYPE || sf->nSpecialType < 0)
			sf->nSpecialType=0;
		str+=S_TYPE[sf->nSpecialType];
		str+="</td>";


		str+="<td>";
		str+=YES_NO[sf->bPk];
		str+="</td>";

		str+="</tr>";
	}


	str+="</table>";


}

void CSearcher::ModifyVConf(HSS& hssPara, string& str)
{

	string& stype = hssPara[MODIFY_VCONF];
	if (stype == "view")
	{
		for (HSS::iterator it = hssPara.begin(); it != hssPara.end(); ++it)
			var_set_one_opt(it->first.c_str(), it->second.c_str(), g_var_set);
	}
	else if (stype == "store")
	{
		for (HSS::iterator it = hssPara.begin(); it != hssPara.end(); ++it)
			var_set_one_opt(it->first.c_str(), it->second.c_str(), g_var_set);
		 var_store_conf(VAR_CONF_FILE, g_var_set);
	}
	else if (stype == "restore")
	{
		var_restore_conf(BAK_VAR_CONF_FILE, VAR_CONF_FILE, g_var_set);
	}
	else
	{
		str = "_modify_vconf=[view|store|restore]";
		return;
	}
	str = "<table border=\"1\" width=\"50%%\">";
	str+="<tr>\
		 <td>变量名称</td>\
		 <td>变量类型</td>\
		 <td>变量值</td>\
		 <td>变量下限</td>\
		 <td>变量上限</td>\
		 </tr>";

	char buf[256];
	for(VAR_SET::iterator it = g_var_set.begin(); it != g_var_set.end(); ++it)
	{
		str += "<tr>";

		str +="<td>";
		str += it->first;
		str +="</td>";

		str +="<td>";
		str += it->second->get_type();
		str +="</td>";

		str +="<td>";
		str += it->second->to_string(buf);
		str +="</td>";

		str +="<td>";
		str += it->second->get_min_buf();
		str +="</td>";


		str +="<td>";
		str += it->second->get_max_buf();
		str +="</td>";


		str += "</tr>";

	}
	str += "</table>";
}

void CSearcher::UpdateStatInfo(int resCnt, int cost)
{
	if (cost < 0)
		cost = 1;
	m_statInfo.nSrchCnt++;
	m_statInfo.nNoResCnt+=(resCnt==0);

	m_statInfo.nTotalTime+=cost;

	if (m_statInfo.nMaxTime<cost)
		m_statInfo.nMaxTime=cost;

	unsigned int pos=m_statInfo.nRecentMark%100;
	++m_statInfo.nRecentMark;

	m_statInfo.arrRecentRes[pos]=cost;
	if (cost>100)
		cost=100;
	m_statInfo.arrTotalSpan[g_timeSpanRuler[cost/10]]++;
}

void CSearcher::InitStatInfo()
{
	memset(&m_statInfo, 0, sizeof(m_statInfo));
	time_t   curStamp;
	time(&curStamp);
	m_statInfo.nFullUpStamp = m_timestamp;
	m_statInfo.nStaticDocCnt = GetStaticDocCnt();
	m_statInfo.nStartStamp = curStamp;
	m_statInfo.nRecentMark = 0;
}


void CSearcher::ScatterResult(vector<SResult>& res, vector<int>& pri, int fid, int unit,int sort_upper)
{
	if (fid < 0 ||  fid > (int)m_vProfiles.size() || m_vProfiles[fid] == NULL)
		return;

	CProfile<int>* pfl=(CProfile<int>* )(m_vProfiles[fid]);
	int scatter_upper = (sort_upper > m_scatterLimit)? m_scatterLimit: sort_upper;
	pfl->ScatterResult(res, pri, unit, scatter_upper);
}

void ScatterResultOpenApi(void* pSearcher, vector<SResult>& res, vector<int>& pri, int fid, int unit,int sort_upper)
{
	if (sort_upper > (int)res.size() || sort_upper < 0)
		return;
	CSearcher* pSr=(CSearcher*)pSearcher;
	pSr->ScatterResult(res, pri, fid, unit, sort_upper);
}
