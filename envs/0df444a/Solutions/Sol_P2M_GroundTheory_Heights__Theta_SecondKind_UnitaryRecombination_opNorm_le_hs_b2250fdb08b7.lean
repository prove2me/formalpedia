-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_opNorm_le_hs_b2250fdb08b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:07.158064+00:00
-- url     : https://prove2.me/submissions/ef2937e0-26f8-4d61-9670-a78e7e9392f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_nonneg_1a2c98d71290
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_sq_0bd4fc15945c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (X : Matrix ι ι ℂ) : ‖X‖ ≤ hs X := by
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (hs_nonneg _) fun v => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, hs_sq, EuclideanSpace.norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
  calc ‖∑ j, X i j * (WithLp.ofLp v) j‖ ^ 2 ≤ (∑ j, ‖X i j‖ * ‖(WithLp.ofLp v) j‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ (∑ j, ‖X i j‖ ^ 2) * ∑ j, ‖(WithLp.ofLp v) j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
