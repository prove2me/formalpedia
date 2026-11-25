-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.norm_sq_convex_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:53.828082+00:00
-- url     : https://prove2.me/submissions/012b3c36-1035-4371-8c16-a7dd0773a5a4

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
theorem _root_.solution {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z w : E) :
    ‖a • z + b • w‖ ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
  have h1 : ‖a • z + b • w‖ ≤ a * ‖z‖ + b * ‖w‖ := by
    calc ‖a • z + b • w‖ ≤ ‖a • z‖ + ‖b • w‖ := norm_add_le _ _
      _ = a * ‖z‖ + b * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : (a * ‖z‖ + b * ‖w‖) ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖z‖ - ‖w‖))]
  calc ‖a • z + b • w‖ ^ 2 ≤ (a * ‖z‖ + b * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
