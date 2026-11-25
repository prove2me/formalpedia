-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_proof_36cd01184c2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:47.269521+00:00
-- url     : https://prove2.me/submissions/e31fcb02-7d6e-42a7-87b2-616d19e12896

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_funField_eq_2c5aa0f58712
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_finiteDimensional_affField_410254da17a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_eventually_affPiece_eq_b181598bce67
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_coordGraded_piece_eq_8acb7bb23761
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_coordGraded_le_secs_e4173d0b1c52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_div_mem_affRing_of_mem_twistMod_32809b3bdbde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution : HilbertPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hy
  obtain ⟨j, hjX⟩ := hy.relevant
  have hj : y j ≠ 0 := fun h =>
    hjX ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr (by simp [h]))
  have hF := isField_affRing hy hj
  have hfun := funField_eq hj hF
  have hfd := finiteDimensional_affField hy hj
  have hev := eventually_affPiece_eq hy hj
  refine ⟨hfun ▸ hfd, hev.mono fun n hn => ?_, hev.mono fun n hn => ?_⟩
  · have hinj : Function.Injective (LinearMap.mulLeft k (y j ^ n)) :=
      mul_right_injective₀ (pow_ne_zero n hj)
    rw [coordGraded_piece_eq hj n,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _), hn,
      Subalgebra.finrank_toSubmodule, hfun, ← IntermediateField.finrank_eq_finrank_subalgebra]
    rfl
  · refine le_antisymm ?_ (coordGraded_le_secs n)
    intro z hz
    have hz1 : z ∈ twistMod k y (n : ℤ) (singleChart hj) :=
      (Submodule.mem_iInf _).mp hz (singleChart hj)
    have hd := div_mem_affRing_of_mem_twistMod hj n hz1
    rw [coordGraded_piece_eq hj n, hn]
    refine ⟨z / y j ^ n, hd, ?_⟩
    rw [LinearMap.mulLeft_apply]
    field_simp
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
