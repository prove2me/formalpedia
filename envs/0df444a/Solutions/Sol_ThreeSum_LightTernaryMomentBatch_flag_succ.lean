-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentBatch.flag_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:02.19498+00:00
-- url     : https://prove2.me/submissions/5b27e93c-cea6-442b-8887-ff7bce57470e

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentRow
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentBatch
import Theorems.Thm_ThreeSum_LightTernaryMomentBatch_flag_zero
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
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
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightMomentZeroDetector.atoms_target
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.LightTernaryMomentBatch.flag_zero

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryMomentBatch
open Light FiniteMomentZeroDetector
attribute [local instance] Classical.propDecidable
namespace ThreeSum.LightTernaryMomentBatch
theorem _root_.solution (hit : ℕ→Prop) (i : ℕ) :
    flag hit (i+1)=(if hit i then 1 else flag hit i) := by
  classical
  have he : (∃ j < i+1, hit j) ↔ (∃ j < i, hit j) ∨ hit i := by
    constructor
    · rintro ⟨j,hj,hh⟩
      by_cases hji : j < i
      · exact Or.inl ⟨j,hji,hh⟩
      · have : j=i := by omega
        subst j
        exact Or.inr hh
    · rintro (⟨j,hj,hh⟩ | hh)
      · exact ⟨j,by omega,hh⟩
      · exact ⟨i,by omega,hh⟩
  unfold flag
  simp only [he]
  by_cases hi : hit i <;> by_cases hp : ∃ j < i, hit j <;> simp [hi,hp]
end ThreeSum.LightTernaryMomentBatch
