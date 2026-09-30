-- Prove2me | solution 1 for ShiQMAErrorIteration.dyadic_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-30T06:25:46.954103+00:00
-- url     : https://prove2.me/submissions/34914c99-0be1-41ed-b13e-83d1cb2fde9e

import Definitions.Def_ShiQMAErrorIteration
import Theorems.Thm_ShiQMAErrorIteration_scaled_error_bound

set_option autoImplicit false
open ShiQMAErrorIteration

private theorem majorityError_bounds {e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1 / 3) :
    0 ≤ majorityError e ∧ majorityError e ≤ e := by
  constructor
  · have h := mul_nonneg (sq_nonneg e) (show 0 ≤ 3 - 2 * e by linarith)
    dsimp [majorityError]
    nlinarith
  · have h := mul_nonneg
      (mul_nonneg he (show 0 ≤ 1 - e by linarith))
      (show 0 ≤ 1 - 2 * e by linarith)
    dsimp [majorityError]
    nlinarith

private theorem error_bounds (r : Nat) : 0 ≤ error r ∧ error r ≤ 1 / 3 := by
  induction r with
  | zero => norm_num [error]
  | succ r ih =>
      have h := majorityError_bounds ih.1 ih.2
      exact ⟨h.1, h.2.trans ih.2⟩

/-- Three initial rounds give a dyadic bound, then each round doubles the exponent. -/
theorem solution (r : Nat) :
    error (r + 3) ≤ ((1 : ℝ) / 2) ^ (2 ^ r) := by
  have h := scaled_error_bound (r + 2)
  have hp : ((7 : ℝ) / 9) ^ (2 ^ (r + 2)) =
      (((7 : ℝ) / 9) ^ 4) ^ (2 ^ r) := by
    rw [pow_add, show (2 : Nat) ^ 2 = 4 by norm_num, Nat.mul_comm, pow_mul]
  rw [hp] at h
  have hq := pow_le_pow_left₀
    (show 0 ≤ ((7 : ℝ) / 9) ^ 4 from pow_nonneg (by norm_num) _)
    (show ((7 : ℝ) / 9) ^ 4 ≤ 1 / 2 by norm_num) (2 ^ r)
  have he := (error_bounds (r + 3)).1
  have h' : 3 * error (r + 3) ≤ ((1 : ℝ) / 2) ^ (2 ^ r) := by
    simpa only [Nat.add_assoc] using h.trans hq
  linarith
