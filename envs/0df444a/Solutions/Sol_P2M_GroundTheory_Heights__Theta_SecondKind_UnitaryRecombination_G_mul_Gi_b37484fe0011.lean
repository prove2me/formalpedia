-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_G_mul_Gi_b37484fe0011
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:58.012832+00:00
-- url     : https://prove2.me/submissions/7e87c5b5-554e-47ab-a7bf-c18084613beb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq

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
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) : G F y τ k * Gi F y τ k = 1 := by
  induction k with
  | zero => simp [G, Gi]
  | succ m ih =>
    simp only [G, Gi]
    rw [show NormedSpace.exp (yy F y m • Evec F τ m) * G F y τ m *
        (Gi F y τ m * NormedSpace.exp (-(yy F y m • Evec F τ m))) =
        NormedSpace.exp (yy F y m • Evec F τ m) * (G F y τ m * Gi F y τ m) *
        NormedSpace.exp (-(yy F y m • Evec F τ m)) by simp only [Matrix.mul_assoc], ih,
      Matrix.mul_one, exp_mul_exp_neg]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
