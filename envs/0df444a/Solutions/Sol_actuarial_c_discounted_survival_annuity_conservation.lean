-- Prove2me | solution 1 for actuarial_c_discounted_survival_annuity_conservation
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T08:35:24.078812+00:00
-- url     : https://prove2.me/submissions/8bac050c-ed4d-40da-88c5-d31e25228ac6

-- Research directed by Alexander Richard Towell (queelius); formal proof by OpenAI Codex.
-- Finite actuarial identity formulated by WillR, informed by S. David Promislow.
-- Lean and Mathlib provide the formal foundations. No mathematical novelty claimed.
import Mathlib
set_option autoImplicit false
open scoped BigOperators
theorem solution (s : ℕ → ℝ)
    (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       v^(j+1) * (s j - s (j+1))) +
      (1-v)*(∑ j ∈ Finset.range n, v^j * s j) +
      v^n * s n = s 0  := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, pow_succ] at *
    nlinarith only [ih]
