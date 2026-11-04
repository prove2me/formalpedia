-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalFibers.right_native_fiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:23.534343+00:00
-- url     : https://prove2.me/submissions/92798712-4119-4278-aa7a-15dc1fc51249

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
import Theorems.Thm_ThreeSum_TernaryJointType_fieldWord_injective
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
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
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryCanonicalFibers
theorem _root_.solution (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (a : ZMod p) :
    (rightNativeFiber (α := α) maps B a).card ≤ Fintype.card I*B := by
  classical
  have hi (i : I) : ((rightNativeFiber (α := α) maps B a).filter fun r => r.1 = i).card ≤ B := by
    let F := (rightNativeFiber (α := α) maps B a).filter fun r => r.1 = i
    by_cases hz : F.card = 0
    · change F.card ≤ B
      rw [hz]
      exact Nat.zero_le B
    obtain ⟨r0,hr0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨hr0,hi0⟩ := mem_filter.mp hr0
    have hdata := (mem_filter.mp hr0).2
    have hb : TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.rightVector (maps i) a ≤ B := by
      have h := hdata.1
      change TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.rightVector (maps r0.1) (rightNative maps r0) ≤ B at h
      simpa [hi0,hdata.2] using h
    have hc : F.card ≤ TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.rightVector (maps i) a := by
      unfold TernaryCoverTrimming.bucketSize
      apply card_le_card_of_injOn (fun r : SourceRecord L α I => fieldWord p r.2.val)
      · intro r hr
        obtain ⟨hr,hri⟩ := mem_filter.mp hr
        have hn := (mem_filter.mp hr).2.2
        apply mem_filter.mpr
        refine ⟨?_,?_⟩
        · exact mem_image.mpr ⟨r.2.val,r.2.property,rfl⟩
        · simpa [rightNative,hri] using hn
      · intro r hr t ht h
        apply Prod.ext
        · exact (mem_filter.mp hr).2.trans (mem_filter.mp ht).2.symm
        · apply Subtype.ext
          exact fieldWord_injective hp h
    exact hc.trans hb
  calc
    _ = ∑ i : I, ((rightNativeFiber (α := α) maps B a).filter fun r => r.1 = i).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _i : I, B := sum_le_sum (fun i _ => hi i)
    _ = _ := by simp
end ThreeSum.TernaryCanonicalFibers
