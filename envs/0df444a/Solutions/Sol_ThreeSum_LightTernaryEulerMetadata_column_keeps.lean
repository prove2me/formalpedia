-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerMetadata.column_keeps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:18.790488+00:00
-- url     : https://prove2.me/submissions/bbf9040f-7b99-4e93-978c-1e4a63e66654

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_rowAddr_ne
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
open ThreeSum ThreeSum.LightTernaryEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThreeSum.LightTernaryEulerMetadata
theorem _root_.solution {μ ν : ℕ → ℤ} {ws N rows i k : ℕ}
    (hi : i<N) (hk : k<N) (hne : i≠k)
    (H : LightTernaryPredecessorTable.KeptApart μ ν (ws+k) N rows) (j : ℕ) :
    ν (rowAddr ws N i j)=μ (rowAddr ws N i j) := by
  apply H
  intro l hl
  constructor
  · convert rowAddr_ne (j := j) (l := l) hi hk hne using 1 <;> simp [rowAddr] <;> omega
  · convert rowAddr_ne (j := j) (l := rows+l) hi hk hne using 1 <;> simp [rowAddr,Nat.mul_add] <;> omega
end ThreeSum.LightTernaryEulerMetadata
