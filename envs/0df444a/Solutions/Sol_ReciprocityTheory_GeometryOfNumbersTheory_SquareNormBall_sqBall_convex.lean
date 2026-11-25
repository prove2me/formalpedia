-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:39.715681+00:00
-- url     : https://prove2.me/submissions/4f38bbb6-39d2-41bf-bee8-4da8a465e7f5

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_norm_sq_convex_comb

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
theorem _root_.solution (r : ℕ) (R : ℝ) : Convex ℝ (sqBall r E R) := by
  intro u hu v hv a b ha hb hab
  simp only [sqBall, Set.mem_setOf_eq] at hu hv ⊢
  calc ∑ k, ‖(a • u + b • v) k‖ ^ 2 = ∑ k, ‖a • u k + b • v k‖ ^ 2 := rfl
    _ ≤ ∑ k, (a * ‖u k‖ ^ 2 + b * ‖v k‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => norm_sq_convex_comb ha hb hab _ _
    _ = a * ∑ k, ‖u k‖ ^ 2 + b * ∑ k, ‖v k‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * R ^ 2 + b * R ^ 2 := by gcongr
    _ = R ^ 2 := by rw [← add_mul, hab, one_mul]
end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
