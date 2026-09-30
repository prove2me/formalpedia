-- Prove2me | solution 1 for ShiQMAErrorIteration.scaled_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-30T06:12:08.863454+00:00
-- url     : https://prove2.me/submissions/c9961e58-7004-4def-aa89-4d78e8ff35f5

import Definitions.Def_ShiQMAErrorIteration

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

private theorem majorityError_square_bound {e : ℝ} (he : 0 ≤ e) :
    3 * majorityError e ≤ (3 * e) ^ 2 := by
  have h := mul_nonneg he (sq_nonneg e)
  dsimp [majorityError]
  nlinarith

/-- After the first round the scaled error squares at every further round. -/
theorem solution (r : Nat) :
    3 * error (r + 1) ≤ ((7 : ℝ) / 9) ^ (2 ^ r) := by
  induction r with
  | zero => norm_num [error, majorityError]
  | succ r ih =>
      have h := majorityError_square_bound (error_bounds (r + 1)).1
      have hs := pow_le_pow_left₀
        (show 0 ≤ 3 * error (r + 1) by linarith [(error_bounds (r + 1)).1]) ih 2
      change 3 * majorityError (error (r + 1)) ≤ ((7 : ℝ) / 9) ^ (2 ^ (r + 1))
      rw [pow_succ, pow_mul]
      exact h.trans hs
