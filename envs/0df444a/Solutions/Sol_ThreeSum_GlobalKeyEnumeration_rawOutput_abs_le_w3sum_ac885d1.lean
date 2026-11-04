-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.rawOutput_abs_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:15:59.720015+00:00
-- url     : https://prove2.me/submissions/2d4b848b-7171-4ee7-bd09-4d87faa2bc51

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_le_sum_abs
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
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



set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution {h L : ℕ} (w : Weight L (LocalField h))
    (Q : Finset (Fin L)) : |rawOutput w Q| ≤ ((L*localPrime h : ℕ) : ℤ) := by
  unfold rawOutput
  calc
    _ ≤ ∑ i : Fin L, |if i ∈ Q then (0 : ℤ) else
        ((w (i,true)).val : ℤ)-((w (i,false)).val : ℤ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin L, (localPrime h : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ Q
      · simp [hi]
      · simp only [hi,ite_false]
        have ht : ((w (i,true)).val : ℤ) < (localPrime h : ℤ) := by
          exact_mod_cast (w (i,true)).val_lt
        have hf : ((w (i,false)).val : ℤ) < (localPrime h : ℤ) := by
          exact_mod_cast (w (i,false)).val_lt
        exact abs_le.mpr ⟨by omega,by omega⟩
    _ = _ := by simp
end ThreeSum.GlobalKeyEnumeration
