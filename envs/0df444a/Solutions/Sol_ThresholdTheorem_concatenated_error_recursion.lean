-- Prove2me | solution 1 for ThresholdTheorem.concatenated_error_recursion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:25:49.260984+00:00
-- url     : https://prove2.me/submissions/b8760ed8-3e00-492e-a318-542f8540cf83

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

theorem solution (c p : ℝ) (hc : 0 < c) (e : ℕ → ℝ)
    (he0 : e 0 ≤ p) (hnn : ∀ k, 0 ≤ e k)
    (hrec : ∀ k, e (k + 1) ≤ c * e k ^ 2) (k : ℕ) :
    e k ≤ (c * p) ^ (2 ^ k) / c := by
  have hscaled : ∀ k, c * e k ≤ (c * p) ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simpa using mul_le_mul_of_nonneg_left he0 hc.le
    | succ k ih =>
      have he := mul_le_mul_of_nonneg_left (hrec k) hc.le
      have hb : 0 ≤ c * e k := mul_nonneg hc.le (hnn k)
      have hs : (c * e k) ^ 2 ≤ ((c * p) ^ (2 ^ k)) ^ 2 :=
        sq_le_sq₀ hb (hb.trans ih) |>.2 ih
      rw [pow_succ, pow_mul]
      nlinarith
  exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hscaled k)

