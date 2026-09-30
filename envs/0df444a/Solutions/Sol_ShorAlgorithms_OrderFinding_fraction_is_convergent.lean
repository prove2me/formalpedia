-- Prove2me | solution 1 for ShorAlgorithms.OrderFinding.fraction_is_convergent
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:56:19.07548+00:00
-- url     : https://prove2.me/submissions/386b28dc-c21a-4813-ad62-1a039447ade7

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false

theorem solution (n q c : ℕ) (hnq : n ^ 2 ≤ q) (s : ℚ) (hs : s.den < n)
    (h : |(c : ℝ) / q - (s : ℝ)| ≤ 1 / (2 * q)) :
    ∃ m : ℕ, s = ((c : ℝ) / q).convergent m := by
  apply Real.exists_rat_eq_convergent
  apply h.trans_lt
  have hd : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hdn : (s.den : ℝ) < n := by exact_mod_cast hs
  have hnq' : (n : ℝ)^2 ≤ q := by exact_mod_cast hnq
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith
