-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-21T17:09:43.082468+00:00
-- url     : https://prove2.me/submissions/92a9b3dc-acbd-4b65-837b-cfbfb10a5085
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_286_to_700
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_log_bound_mid
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large
import Mathlib

set_option maxRecDepth 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace TaoFivePrimes

/-! ### Exponentiating the log-form bound

On $x \ge 700$ the logarithmic Rosser–Schoenfeld bound exponentiates back to
the product form (3.29): every factor $p/(p-1)$ is positive, so `Real.log_prod`
turns the sum of logs into the log of the product, and strict monotonicity of
`Real.exp` (`Real.exp_lt_exp`) transfers the inequality. The right-hand side
then simplifies by `Real.exp_add` and `Real.exp_log`, using $\log x > 0$ and
$1 + 1/(2\log^2 x) > 0$ on this range. -/

theorem exp_log_prod_bound {x : ℝ} (hx : 700 ≤ x)
    (h : ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2))) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have hf : ∀ p ∈ Nat.primesLE ⌊x⌋₊, 0 < (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have h2 : 2 ≤ p := ((Nat.mem_primesLE.mp hp).2).two_le
    have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast h2
    exact div_pos (by linarith) (by linarith)
  have hne : ∀ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ) / ((p : ℝ) - 1)) ≠ 0 :=
    fun p hp => ne_of_gt (hf p hp)
  have hprod : 0 < ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_pos hf
  have hlog : Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)) =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) :=
    Real.log_prod hne
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hfac : 0 < 1 + 1 / (2 * (Real.log x) ^ 2) := by
    have h2 : (0 : ℝ) ≤ 2 * (Real.log x) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h3 : (0 : ℝ) ≤ 1 / (2 * (Real.log x) ^ 2) := one_div_nonneg.mpr h2
    linarith
  have hrw : Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log x) +
      Real.log (1 + 1 / (2 * (Real.log x) ^ 2))) =
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hlx, Real.exp_log hfac]
  calc ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)
      = Real.exp (Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1))) :=
        (Real.exp_log hprod).symm
    _ < Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2))) := by
        rw [hlog]
        exact Real.exp_lt_exp.mpr h
    _ = Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := hrw

theorem solution (x : ℝ) (hx : 286 ≤ x) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  rcases lt_or_ge x 700 with h700 | h700
  · exact rosser_schoenfeld_product_bound_286_to_700 x hx h700
  · by_cases h1e8 : x ≤ 10 ^ 8
    · exact exp_log_prod_bound h700
        (rosser_schoenfeld_product_log_bound_mid x h700 h1e8)
    · exact exp_log_prod_bound h700
        (rosser_schoenfeld_product_log_bound_large x (le_of_lt (not_le.mp h1e8)))

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (x : ℝ) (hx : 286 ≤ x) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) :=
  TaoFivePrimes.solution x hx

#print axioms solution
