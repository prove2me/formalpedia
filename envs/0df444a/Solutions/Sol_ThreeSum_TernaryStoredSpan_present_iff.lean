-- Prove2me | solution 1 for ThreeSum.TernaryStoredSpan.present_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:26.677612+00:00
-- url     : https://prove2.me/submissions/2b73a4ca-6bdc-4ea0-a0de-f0b9a44d57dd

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}
namespace ThreeSum.TernaryStoredSpan
theorem _root_.solution [Fact p.Prime] (f : ℕ → ℕ → ℕ) (n : ℕ)
    (rows : List (Fin J → ZMod p)) (row : Fin J → ZMod p)
    (H : Represents f n rows) (hf : ∀ k<n, ∀ i<J, f k i<p) :
    LightSpanCatalogTest.Present (fun k i => (f k i : ℤ))
      (fun i => if hi : i<J then ((row ⟨i,hi⟩).val : ℤ) else 0) J n ↔
      row∈Submodule.span (ZMod p) {v | v∈rows} := by
  rw [H row]
  constructor
  · rintro ⟨k,hk,he⟩
    refine ⟨k,hk,?_⟩
    intro i
    have hh := he i.val i.isLt
    simp only [dif_pos i.isLt] at hh
    have hn : f k i.val=(row i).val := by exact_mod_cast hh
    rw [hn,ZMod.natCast_zmod_val]
  · rintro ⟨k,hk,he⟩
    refine ⟨k,hk,?_⟩
    intro i hi
    have hh := congrArg ZMod.val (he ⟨i,hi⟩)
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (hf k hk i hi),hi] using
      congrArg (fun x : ℕ => (x : ℤ)) hh
end ThreeSum.TernaryStoredSpan
