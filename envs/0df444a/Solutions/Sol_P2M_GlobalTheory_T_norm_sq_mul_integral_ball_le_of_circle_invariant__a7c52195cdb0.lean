-- Prove2me | solution 1 for P2M_GlobalTheory_T_norm_sq_mul_integral_ball_le_of_circle_invariant__a7c52195cdb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:40.214923+00:00
-- url     : https://prove2.me/submissions/a534cbcb-4374-418e-8b1e-5febf7e8f3e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulIntegralBallLeOfCircleInvariant
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulIntegralBallLeOfCircleInvariantStatement
import Theorems.Thm_GlobalTheory_norm_sq_mul_integral_ball_le_of_circle_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (δ : ℝ) (U : Set (V n)) (f : V n → ℂ) (W : V n → ℝ), 0 < δ → IsOpen U → closedBall 0 δ ⊆ U → DifferentiableOn ℂ f U → ContinuousOn W (closedBall 0 δ) → (∀ w, 0 ≤ W w) → (∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → W (θ • w) = W w) → ‖f 0‖ ^ 2 * ∫ w in ball (0 : V n) δ, W w ≤ ∫ w in ball (0 : V n) δ, ‖f w‖ ^ 2 * W w := by
  first | exact @GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant | exact GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant | (intros; apply GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant <;> assumption)
end _root_.GlobalTheory.T
