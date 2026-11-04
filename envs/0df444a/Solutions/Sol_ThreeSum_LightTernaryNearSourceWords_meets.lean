-- Prove2me | solution 1 for ThreeSum.LightTernaryNearSourceWords.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:59.04162+00:00
-- url     : https://prove2.me/submissions/48579d02-ee72-46b0-85d8-062564830499

import Definitions.Def_Submission_ThreeSum_LightTernaryNearSource
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSourceWords
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_address
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_lt_pow_two
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_bank_index_correct
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_near_index_correct
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_near_predecessor_present
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_numerator
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_physical_near
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_bank_read
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_bound
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_precedes
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowWeight_eq
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryNearSourceWords
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryPhysicalEuler
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearSourceWords
theorem _root_.solution {pMain pRanks pMetadata pMemo pColumn pCell pDigit pZero pErase pRank pSearch
    pScan pFill pRow pSum pDivide pNaturalDivide N a rows powers bank nb bv L T activeBase ws rankBase
    vals h pcount fr U V d : ℕ}
    (hmain : P[pMain]?=some (LightTernaryNearSource.body pRanks pMetadata pMemo))
    (hranks : P[pRanks]?=some (LightTernaryRankTable.body pRank))
    (hmetadata : P[pMetadata]?=some (LightTernaryEulerMetadata.body pColumn))
    (hmemo : P[pMemo]?=some (LightTernaryEulerMemo.body pScan))
    (hcolumn : P[pColumn]?=some (LightTernaryPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]?=some (LightTernaryPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hscan : P[pScan]?=some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (Q : TritWord N) (bankWords nearWords : ℕ → TritWord N)
    (source : TritWord N → ℤ) (homogeneous : ∀ A, source A≠0 → rank A=h)
    (F : ∀ current, T<current → current≤2*N → Light.Emod.Pre lim (current-h) V fr)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+rows≤ws) (hb : bank+nb≤ws) (hp : powers+(2*N+1)≤ws)
    (hactiveSpace : activeBase+N≤ws) (hbankVals : bv+nb≤ws)
    (hmetadataRanks : ws+2*N*rows+N≤rankBase)
    (hrankVals : rankBase+rows≤vals) (hvals : vals+rows≤fr) (hfr : fr≤lim.space)
    (hcount : vals+rows≤pcount) (hspace : pcount≤lim.space)
    (hword : ((nb+rows+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+N+32 : ℕ) : ℤ)≤lim.word)
    (hmemoWord : ((N+rows+2*N+h+20 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<rows, μ (a+j)=(address (nearWords j) : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(address (bankWords j) : ℤ))
    (hactiveRead : ∀ i<N, μ (activeBase+i)=1)
    (hbankSorted : ∀ j k, j<k → k<nb → address (bankWords j)<address (bankWords k))
    (hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k))
    (hpowers : Powers μ powers (2*N))
    (hL : L≤2*N) (hnb : nb<2^L) (hnn : rows<2^L) (hnbpos : 0<nb)
    (hbankPresent : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → T<rank W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ T<rank (nearWords j))
    (hT : T≤2*N) (hh : h≤T)
    (hbankValues : ∀ j<nb, μ (bv+j)=binomialZeta source (bankWords j))
    (hvalue : ∀ R, |binomialZeta source R|≤U)
    (hV : 2*(N+1)*U≤V) (hd : d+2*N+7≤lim.depth) :
    Meets lim P pMain d [N,a,rows,powers,bank,nb,bv,L,T,activeBase,ws,rankBase,vals,h,2*N,pcount,fr]
      μ (LightTernaryNearSource.time N L rows (2*N-T) V)
      (fun r ν => r=0 ∧ Kept μ ν ws ∧ ∀ j<rows, ν (vals+j)=binomialZeta source (nearWords j)) := by
  let codes := fun j => address (nearWords j)
  let bi := fun i j => predecessorOrdinal bankWords nb (nearWords j) i
  let ni := fun i j => predecessorOrdinal nearWords rows (nearWords j) i
  let g := physicalValue (binomialZeta source) bankWords nearWords bv vals
  have hsep : bv+nb≤vals := by omega
  have rankEq (j : ℕ) : LightTernaryNearSource.ranks N codes j=rank (nearWords j) :=
    LightTernaryRank.partialRank_address _
  have hkey (j i : ℕ) : LightTernaryNearSource.keys N rows T bv vals codes (fun _ => 1) bi ni j i=
      rowKey (nearWords j) bankWords nearWords nb rows T bv vals i := rfl
  have hweight (j i : ℕ) : LightTernaryNearSource.weights N codes (fun _ => 1) j i=
      rowWeight (nearWords j) i := rfl
  apply LightTernaryNearSource.meets hmain hranks hmetadata hmemo hcolumn hcell hdigit hzero herase hrank hsearch
    hscan hfill hrow hsum hdivide hnatural μ codes (fun j => address (bankWords j)) (fun _ => 1) bi ni
    g (fun j => binomialZeta source (nearWords j)) F hw ha hb hp hactiveSpace hbankVals hmetadataRanks
    hrankVals hvals hfr hspace hword hcontrols hmemoWord hread hbankRead hactiveRead hbankSorted hnearSorted
    hpowers (fun j _ => address_lt_pow_two _) hL hnb hnn hnbpos (fun _ _ => by decide)
  · intro i hi j hj _ hdigit hpred
    exact bank_index_correct bankWords hbankPresent (nearWords j) i hi hdigit hpred
  · intro i hi j hj _ hdigit hpred
    exact near_index_correct Q (nearWords j) nearWords hnearPresent (hnearRows j hj).1 i hi hdigit hpred
  · exact hT
  · exact hh
  · intro j hj
    rw [rankEq]
    refine ⟨(hnearRows j hj).2,?_⟩
    calc
      rank (nearWords j)≤∑ _i : Fin N, 2 := Finset.sum_le_sum (fun i _ => by have := (nearWords j i).isLt; omega)
      _=2*N := by simp; omega
  · intro j hj i hi
    rw [hkey]
    have hk := rowKey_bound Q (nearWords j) bankWords nearWords hsep hnbpos hbankPresent hnearPresent
      (hnearRows j hj).1 ⟨i,hi⟩
    dsimp only at hk
    exact ⟨by omega,by omega⟩
  · intro j hj i hi hk
    rw [hkey] at hk ⊢
    obtain ⟨k,hk,he,hread⟩ := rowKey_bank_read Q (nearWords j) bankWords nearWords (binomialZeta source) μ
      hsep hnbpos hbankPresent hnearPresent (hnearRows j hj).1 hbankValues ⟨i,hi⟩ hk
    dsimp only at he hread
    exact ⟨by omega,hread⟩
  · intro j hj
    exact congrArg (binomialZeta source) (physical_near bankWords nearWords)
  · intro j hj i hi
    rw [hweight,rowWeight_eq (nearWords j) ⟨i,hi⟩]
    exact Nat.le_of_lt_succ (nearWords j ⟨i,hi⟩).isLt
  · intro j hj i hi
    exact hvalue _
  · intro j hj i hi
    rw [hkey]
    rcases rowKey_precedes Q (nearWords j) bankWords nearWords hsep hnbpos hbankPresent hnearPresent
      (hnearRows j hj).1 ⟨i,hi⟩ with hb | ⟨k,hk,he,hr⟩
    · exact Or.inl hb
    · exact Or.inr ⟨k,hk,he,by simpa only [rankEq] using hr⟩
  · intro j hj
    simp only [hweight,hkey,rankEq]
    exact numerator (nearWords j) bankWords nearWords source homogeneous (hh.trans (Nat.le_of_lt (hnearRows j hj).2))
      hsep hbankPresent (near_predecessor_present Q (nearWords j) nearWords hnearPresent (hnearRows j hj).1)
  · exact hV
  · exact hd
end ThreeSum.LightTernaryNearSourceWords
