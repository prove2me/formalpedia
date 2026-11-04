-- Prove2me | solution 1 for ThreeSum.WeightedKernel.memo_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:24.807838+00:00
-- url     : https://prove2.me/submissions/03068909-8e51-4ce4-a8e2-bb294206a423

import Definitions.Def_Submission_Weighted_NearSourceWords
import Definitions.Def_Submission_Weighted_BankStages
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_LightEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Definitions.Def_Submission_Weighted_NearSetup
import Definitions.Def_Submission_Weighted_KernelProgram
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedKernel
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
open ThreeSum.WeightedBankStageModel ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
namespace ThreeSum.WeightedKernel
theorem _root_.solution {N a rows powers bank nb bv L T activeBase ws rankBase
    vals h pcount fr U V d : ℕ}
    (μ : ℕ → ℤ) (Q : TritWord N) (bankWords nearWords : ℕ → TritWord N)
    (source : TritWord N → ℤ) (homogeneous : ∀ A, source A≠0 → rank A=h)
    (F : ∀ current, h<current → current≤2*N → Light.Emod.Pre lim (current-h) V fr)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+rows≤ws) (hb : bank+nb≤ws) (hp : powers+(2*N+1)≤ws)
    (hactiveSpace : activeBase+N≤ws) (hbankVals : bv+nb≤ws)
    (hmetadataRanks : ws+2*N*rows+N≤rankBase)
    (hrankVals : rankBase+rows≤vals) (hvals : vals+rows≤fr) (hfr : fr≤lim.space)
    (hcount : vals+rows≤pcount) (hspace : pcount≤lim.space)
    (hword : ((nb+rows+2^(2*N+1)+1025*N+1100 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+N+32 : ℕ) : ℤ)≤lim.word)
    (hmemoWord : ((N+rows+2*N+h+20 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<rows, μ (a+j)=(address (nearWords j) : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(address (bankWords j) : ℤ))
    (hactiveRead : ∀ i<N, μ (activeBase+i)=1)
    (hbankSorted : ∀ j k, j<k → k<nb → address (bankWords j)<address (bankWords k))
    (hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k))
    (hpowers : Powers μ powers (2*N))
    (hL : L≤2*N) (hnb : nb<2^L) (hnn : rows<2^L) (hnbpos : 0<nb)
    (hbankPresent : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → T<cacheCost W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ T<cacheCost (nearWords j))
    (hT : h≤2*N) (hh : 1025*h≤2*T)
    (hbankValues : ∀ j<nb, μ (bv+j)=binomialZeta source (bankWords j))
    (hvalue : ∀ R, |binomialZeta source R|≤U)
    (hV : 2*(N+1)*U≤V) (hd : d+2*N+7≤lim.depth) :
    Meets lim program 0 d [N,a,rows,powers,bank,nb,bv,L,T,activeBase,ws,rankBase,vals,h,2*N,pcount,fr]
      μ (LightWeightedNearSource.time N L rows (2*N-h) V)
      (fun r ν => r=0 ∧ Kept μ ν ws ∧ ∀ j<rows, ν (vals+j)=binomialZeta source (nearWords j)) := by
  exact LightWeightedNearSourceWords.meets
    (P := program) (pMain := 0) (pRanks := 1) (pMetadata := 2) (pMemo := 3)
    (pColumn := 5) (pCell := 8) (pDigit := 7) (pZero := 11) (pErase := 10)
    (pRank := 4) (pCost := 12) (pSearch := 13) (pScan := 6) (pFill := 9)
    (pRow := 14) (pSum := 15) (pDivide := 16) (pNaturalDivide := 17)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    μ Q bankWords nearWords source homogeneous F hw ha hb hp hactiveSpace hbankVals
    hmetadataRanks hrankVals hvals hfr hcount hspace hword hcontrols hmemoWord
    hread hbankRead hactiveRead hbankSorted hnearSorted hpowers hL hnb hnn hnbpos
    hbankPresent hnearPresent hnearRows hT hh hbankValues hvalue hV hd
end ThreeSum.WeightedKernel
