-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.box_subset_sqBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:45.342996+00:00
-- url     : https://prove2.me/submissions/91d66f85-42d9-45ae-b0b0-53e3f4db3af4

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
theorem _root_.solution (r : ℕ) {R : ℝ} :
    Set.pi Set.univ (fun _ : Fin r => Metric.closedBall (0 : E) (R / Real.sqrt r)) ⊆
      sqBall r E R := by
  intro u hu
  rw [Set.mem_univ_pi] at hu
  simp only [sqBall, Set.mem_setOf_eq]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
    positivity
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hb : ∀ k, ‖u k‖ ^ 2 ≤ R ^ 2 / r := by
    intro k
    have h := mem_closedBall_zero_iff.mp (hu k)
    calc ‖u k‖ ^ 2 ≤ (R / Real.sqrt r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = R ^ 2 / r := by rw [div_pow, Real.sq_sqrt hr'.le]
  calc ∑ k, ‖u k‖ ^ 2 ≤ ∑ _k : Fin r, R ^ 2 / r := Finset.sum_le_sum fun k _ => hb k
    _ = R ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
