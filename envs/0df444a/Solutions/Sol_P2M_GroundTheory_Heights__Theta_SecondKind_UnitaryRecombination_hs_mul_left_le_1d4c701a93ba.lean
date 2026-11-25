-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_mul_left_le_1d4c701a93ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:36.034398+00:00
-- url     : https://prove2.me/submissions/9c21f45f-0443-47ff-8414-3120e5a16871

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
theorem _root_.solution (A X : Matrix ι ι ℂ) : hs (A * X) ≤ ‖A‖ * hs X := by
  refine (sq_le_sq₀ (hs_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [hs_sq, mul_pow, hs_sq, Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have key := (toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 fun i => X i j)
  rw [l2_opNorm_toEuclideanCLM] at key
  have key2 := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at key2
  convert key2 using 2
  rw [ofLp_toEuclideanCLM]
  simp [mulVec, dotProduct, mul_apply]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
