-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T13:37:57.647748+00:00
-- url     : https://prove2.me/submissions/3ce542d4-14f7-49c2-b192-ecd2fee7d406

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_to_286
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_finite
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_505_to_700
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_700_to_1500
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_1500_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace TaoFivePrimes

/-! ### The (3.29) → (4.10) bridge on [286, 505]

Rosser–Schoenfeld (3.29) bounds the product by $e^\gamma \log x (1 + 1/(2\log^2 x))$,
while (4.10) uses $e^\gamma \log x + 2e^\gamma/\sqrt{x}$. Expanding the first
expression gives $e^\gamma \log x + e^\gamma/(2\log x)$, so it suffices that
$1/(2\log x) \le 2/\sqrt{x}$, i.e. $\sqrt{x} \le 4\log x$. On $[286, 505]$ this
holds by a two-endpoint comparison: $\sqrt{x} \le \sqrt{505} < 22.4723 < 22.52
\le 4\log x$. -/

theorem log_286_gt563 : (5.63 : ℝ) < Real.log 286 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 286)]
  have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
    rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
  have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.630000)
    (by norm_num : (0.630000 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
  have s1 : Real.exp ((5 : ℝ) + 0.630000) ≤
      (2.7182818286 : ℝ) ^ 5 * Real.exp 0.630000 := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.630000)
  have s2 := mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
  rw [show (5.63 : ℝ) = (5 : ℝ) + 0.630000 by norm_num]
  refine lt_of_le_of_lt (le_trans s1 s2) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem sqrt_le_four_log (x : ℝ) (hx : 286 ≤ x) (hx' : x ≤ 505) :
    Real.sqrt x ≤ 4 * Real.log x := by
  have hs505 : Real.sqrt 505 < 22.4723 := by
    rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 505) (by norm_num : (0 : ℝ) ≤ 22.4723)]
    norm_num
  have hln : 5.63 < Real.log x :=
    lt_of_lt_of_le log_286_gt563 (Real.log_le_log (by norm_num : (0 : ℝ) < 286) hx)
  have hc : Real.sqrt x < 4 * Real.log x :=
    calc Real.sqrt x ≤ Real.sqrt 505 := Real.sqrt_le_sqrt hx'
      _ < 22.4723 := hs505
      _ < 22.52 := by norm_num
      _ ≤ 4 * Real.log x := by
        rw [show (22.52 : ℝ) = 4 * 5.63 from by norm_num]
        exact mul_le_mul_of_nonneg_left hln.le (by norm_num)
  exact hc.le

theorem bridge_329_le_410 (x : ℝ) (hx : 286 ≤ x) (hx' : x ≤ 505) :
    Real.exp Real.eulerMascheroniConstant * Real.log x * (1 + 1 / (2 * (Real.log x) ^ 2)) ≤
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hlx : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hpx : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith : (0 : ℝ) < x)
  have hs : Real.sqrt x ≤ 4 * Real.log x := sqrt_le_four_log x hx hx'
  have h2ls : (0 : ℝ) < 2 * Real.log x := by linarith
  have hg : (0 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := Real.exp_nonneg _
  have hsplit :
      Real.exp Real.eulerMascheroniConstant * Real.log x * (1 + 1 / (2 * (Real.log x) ^ 2)) =
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        Real.exp Real.eulerMascheroniConstant / (2 * Real.log x) := by
    field_simp
  rw [hsplit]
  have h3 : Real.exp Real.eulerMascheroniConstant / (2 * Real.log x) ≤
      2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
    rw [div_le_div_iff₀ h2ls hpx]
    calc Real.exp Real.eulerMascheroniConstant * Real.sqrt x ≤
          Real.exp Real.eulerMascheroniConstant * (4 * Real.log x) :=
          mul_le_mul_of_nonneg_left hs hg
      _ = 2 * Real.exp Real.eulerMascheroniConstant * (2 * Real.log x) := by ring
  linarith

/-! ### Main theorem: dispatch over the five range results -/

theorem solution (x : ℝ) (hx : 0 < x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 286 with h | h
  · exact rosser_schoenfeld_product_bound_to_286 x hx h
  · rcases lt_or_ge x 505 with h2 | h2
    · have h700 : x < 700 := lt_of_lt_of_le h2 (by norm_num)
      have hA := rosser_schoenfeld_product_bound_finite x h h700
      exact lt_of_lt_of_le hA (bridge_329_le_410 x h h2.le)
    · rcases lt_or_ge x 700 with h3 | h3
      · exact rosser_schoenfeld_product_bound_505_to_700 x h2 h3
      · rcases lt_or_ge x 1500 with h4 | h4
        · exact rosser_schoenfeld_product_bound_700_to_1500 x h3 h4.le
        · rcases eq_or_lt_of_le h4 with rfl | h4
          · exact rosser_schoenfeld_product_bound_700_to_1500 _ h3 (le_refl _)
          · exact rosser_schoenfeld_product_bound_1500_to_1e8 x h4 hx'

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (x : ℝ) (hx : 0 < x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
