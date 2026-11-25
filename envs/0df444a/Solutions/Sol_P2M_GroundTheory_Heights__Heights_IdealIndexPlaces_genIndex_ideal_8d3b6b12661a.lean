-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_ideal_8d3b6b12661a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:53.956679+00:00
-- url     : https://prove2.me/submissions/0b0ab68e-0b6d-4296-b1f5-ba45de7187b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIdealIndexPlaces
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_absNorm_eq_index_aad97d015a0a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.IdealIndexPlaces
namespace GroundTheory.Heights₂.Heights.IdealIndexPlaces
theorem _root_.solution {L : Type*} [Field L] [NumberField L] {A B : Ideal (𝓞 L)} (hA : A ≠ ⊥)
    (hB : B ≠ ⊥) : genIndex A.toAddSubgroup B.toAddSubgroup = (B.absNorm : ℝ) / A.absNorm := by
  have hAB : A ⊓ B ≠ ⊥ := fun h ↦ (mul_ne_zero hA hB) (le_bot_iff.mp (h ▸ Ideal.mul_le_inf))
  have hn : (A ⊓ B).absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hAB
  have hAn : A.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hA
  have hBn : B.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
  have h1 : B.toAddSubgroup.relIndex A.toAddSubgroup * A.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_left A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_left, absNorm_eq_index]
    rfl
  have h2 : A.toAddSubgroup.relIndex B.toAddSubgroup * B.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_right, absNorm_eq_index]
    rfl
  have h1' : (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / A.absNorm := by
    rw [← h1]; push_cast; field_simp
  have h2' : (A.toAddSubgroup.relIndex B.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / B.absNorm := by
    rw [← h2]; push_cast; field_simp
  unfold genIndex
  rw [h1', h2']
  field_simp
end GroundTheory.Heights₂.Heights.IdealIndexPlaces
