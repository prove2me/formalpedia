-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_theta_exists_corrected
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T09:28:10.475004+00:00
-- url     : https://prove2.me/submissions/c283fb30-b1f3-45bc-b9ca-12b73125d4de

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_totient_theta_exists_corrected`

For `log n ≥ 294` we must exhibit `y` with
`288 ≤ log n + y`, `log n < θ(log n + y)`,
`0 ≤ y - 2 ≤ 0.9 log n/log log n`.

Following §9 of Rosser–Schoenfeld (1962), p. 89, the construction splits into
two ranges, and the reduction is to the two `θ` lower bounds:

* `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite` (Theorem 19):
  `t - 2√t < θ(t)` for `255 ≤ t ≤ 1420`. For `255 ≤ log n ≤ 1340` one takes
  `y = 2 + 2√(1 + log n)`; then `log n + y = (√(1 + log n) + 1)^2` so that
  `log n = (log n + y) - 2√(log n + y)`, giving `log n < θ(log n + y)`.

* `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic` (Theorem 4, (3.14)):
  `t(1 - 1/(2 log t)) < θ(t)` for `1340 ≤ t`. For `log n ≥ 1340` one takes
  `y = 2 + (0.9 log n)/log log n`; since `t = log n + y` satisfies
  `2 y log t ≥ 1.8 log n ≥ log n + y = t`, we get
  `log n ≤ t - t/(2 log t) < θ(t)`.

In both ranges the hypotheses `288 ≤ log n + y` and
`0 ≤ y - 2 ≤ 0.9 log n/log log n` are elementary estimates.
-/

namespace TaoFivePrimes

theorem solution (n : ℕ) (hn : 3 ≤ n) (hlog : 294 ≤ Real.log (n : ℝ)) :
    ∃ y : ℝ, 288 ≤ Real.log (n : ℝ) + y ∧
      Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y) ∧
      0 ≤ y - 2 ∧ y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := by
  have hMpos : 0 < Real.log (n : ℝ) := by linarith
  have hLpos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos (by linarith)
  by_cases hcase : Real.log (n : ℝ) ≤ 1340
  · refine ⟨2 + 2 * Real.sqrt (1 + Real.log (n : ℝ)), ?_, ?_, ?_, ?_⟩
    · have h1 := Real.sqrt_nonneg (1 + Real.log (n : ℝ))
      linarith
    · have hs1 : Real.sqrt (1 + Real.log (n : ℝ)) ^ 2 = 1 + Real.log (n : ℝ) :=
        Real.sq_sqrt (by linarith)
      have hsqrt_ub : Real.sqrt (1 + Real.log (n : ℝ)) ≤ 37 := by
        have h : Real.sqrt (1 + Real.log (n : ℝ)) ≤ Real.sqrt 1369 :=
          Real.sqrt_le_sqrt (by linarith)
        rwa [show (1369 : ℝ) = 37 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
      have ht1 : 255 ≤ Real.log (n : ℝ) + (2 + 2 * Real.sqrt (1 + Real.log (n : ℝ))) := by
        have h := Real.sqrt_nonneg (1 + Real.log (n : ℝ))
        linarith
      have ht2 : Real.log (n : ℝ) + (2 + 2 * Real.sqrt (1 + Real.log (n : ℝ))) ≤ 1420 := by
        linarith
      have hchild := rosser_schoenfeld_theta_lower_finite
        (Real.log (n : ℝ) + (2 + 2 * Real.sqrt (1 + Real.log (n : ℝ)))) ht1 ht2
      have hteq : Real.log (n : ℝ) +
            (2 + 2 * Real.sqrt (1 + Real.log (n : ℝ))) -
            2 * Real.sqrt (Real.log (n : ℝ) + (2 + 2 * Real.sqrt (1 + Real.log (n : ℝ)))) =
          Real.log (n : ℝ) := by
        have hsq : Real.log (n : ℝ) + (2 + 2 * Real.sqrt (1 + Real.log (n : ℝ))) =
            (Real.sqrt (1 + Real.log (n : ℝ)) + 1) ^ 2 := by
          rw [add_sq, hs1]
          ring
        have hsqt : Real.sqrt (Real.log (n : ℝ) + (2 + 2 * Real.sqrt (1 + Real.log (n : ℝ)))) =
            Real.sqrt (1 + Real.log (n : ℝ)) + 1 := by
          rw [hsq, Real.sqrt_sq (by positivity)]
        rw [hsqt]
        nlinarith [hs1]
      linarith
    · have h := Real.sqrt_nonneg (1 + Real.log (n : ℝ))
      linarith
    · have hLub : Real.log (Real.log (n : ℝ)) ≤ 7.25 := by
        rw [Real.log_le_iff_le_exp hMpos]
        have he7 : (2.7182818283 : ℝ) ^ 7 ≤ Real.exp 7 := by
          rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
          exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
            (le_of_lt Real.exp_one_gt_d9) 7
        have he025 : (1.25 : ℝ) ≤ Real.exp 0.25 := by
          have h := Real.add_one_le_exp (0.25 : ℝ)
          linarith
        have hexp : Real.exp 7.25 = Real.exp 7 * Real.exp 0.25 := by
          rw [← Real.exp_add]
          norm_num
        calc Real.log (n : ℝ) ≤ 1340 := hcase
          _ ≤ (2.7182818283 : ℝ) ^ 7 * 1.25 := by norm_num
          _ ≤ Real.exp 7 * Real.exp 0.25 :=
              mul_le_mul he7 he025 (by norm_num) (by positivity)
          _ = Real.exp 7.25 := hexp.symm
      have hgoal : 2 * Real.sqrt (1 + Real.log (n : ℝ)) ≤
          0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := by
        have hmain : 2 * Real.sqrt (1 + Real.log (n : ℝ)) ≤
            0.9 * Real.log (n : ℝ) / 7.25 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 7.25)]
          have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + Real.log (n : ℝ) by linarith)
          have hA : (14.5 * Real.sqrt (1 + Real.log (n : ℝ))) ^ 2 ≤
              (0.9 * Real.log (n : ℝ)) ^ 2 := by
            nlinarith [hs, hcase, hlog, sq_nonneg (Real.log (n : ℝ) - 294)]
          have habs := sq_le_sq.mp hA
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at habs
          linarith
        have hfin : 0.9 * Real.log (n : ℝ) / 7.25 ≤
            0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) hLpos hLub
        linarith
      have h := Real.sqrt_nonneg (1 + Real.log (n : ℝ))
      linarith
  · push Not at hcase
    refine ⟨2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)), ?_, ?_, ?_, ?_⟩
    · have h := div_nonneg (by positivity : (0 : ℝ) ≤ 0.9 * Real.log (n : ℝ)) hLpos.le
      linarith
    · have hy_nonneg : 0 ≤ 2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := by
        positivity
      have hL_lb : 7.1 ≤ Real.log (Real.log (n : ℝ)) := by
        rw [Real.le_log_iff_exp_le hMpos]
        have he01 : Real.exp 0.1 ≤ 1.11 := by
          have h := Real.exp_bound' (show (0 : ℝ) ≤ 0.1 by norm_num)
            (show (0.1 : ℝ) ≤ 1 by norm_num) (show (0 : ℕ) < 2 by norm_num)
          norm_num [Finset.sum_range_succ, Nat.factorial] at h
          linarith
        have he7u : Real.exp 7 ≤ (2.7182818286 : ℝ) ^ 7 := by
          rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
          exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) Real.exp_one_lt_d9.le 7
        have he71 : Real.exp 7.1 = Real.exp 7 * Real.exp 0.1 := by
          rw [← Real.exp_add]
          norm_num
        calc Real.exp 7.1 = Real.exp 7 * Real.exp 0.1 := he71
          _ ≤ (2.7182818286 : ℝ) ^ 7 * 1.11 :=
              mul_le_mul he7u he01 (by positivity) (by norm_num)
          _ ≤ Real.log (n : ℝ) := by
              have : (2.7182818286 : ℝ) ^ 7 * 1.11 ≤ 1340 := by norm_num
              linarith
      have hlogt_ge : Real.log (Real.log (n : ℝ)) ≤
          Real.log (Real.log (n : ℝ) + (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) :=
        Real.log_le_log hMpos (by linarith)
      have hlogt_pos : 0 < Real.log (Real.log (n : ℝ) +
          (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) := by
        linarith
      have hprod : 0.9 * Real.log (n : ℝ) ≤
          (0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) *
            Real.log (Real.log (n : ℝ) +
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) := by
        have hratio : 1 ≤ Real.log (Real.log (n : ℝ) +
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) /
            Real.log (Real.log (n : ℝ)) :=
          (one_le_div hLpos).mpr hlogt_ge
        calc 0.9 * Real.log (n : ℝ) = 0.9 * Real.log (n : ℝ) * 1 := by ring
          _ ≤ 0.9 * Real.log (n : ℝ) * (Real.log (Real.log (n : ℝ) +
                (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) /
              Real.log (Real.log (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = (0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) *
              Real.log (Real.log (n : ℝ) +
                (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) := by ring
      have hy_le : 2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤
          0.8 * Real.log (n : ℝ) := by
        have hdiv2 : 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤
            0.9 * Real.log (n : ℝ) / 7.1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hL_lb
        have h78 : 0.9 * Real.log (n : ℝ) / 7.1 ≤ 0.8 * Real.log (n : ℝ) - 2 := by
          have hrew : 0.9 * Real.log (n : ℝ) / 7.1 = Real.log (n : ℝ) * (0.9 / 7.1) := by
            ring
          nlinarith [hcase, hrew]
        linarith
      have hkey : Real.log (n : ℝ) ≤
          (Real.log (n : ℝ) + (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) *
            (1 - 1 / (2 * Real.log (Real.log (n : ℝ) +
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))))) := by
        have hy_log : (0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) *
              Real.log (Real.log (n : ℝ) +
                (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) ≤
            (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) *
              Real.log (Real.log (n : ℝ) +
                (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right _ hlogt_pos.le
          linarith
        have ht_le : Real.log (n : ℝ) + (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ≤
            2 * ((2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) *
              Real.log (Real.log (n : ℝ) +
                (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))))) := by
          nlinarith [hprod, hy_log, hy_le, hcase]
        have h2log : 0 < 2 * Real.log (Real.log (n : ℝ) +
            (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) := by
          linarith
        have hdiv3 : (Real.log (n : ℝ) +
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) /
              (2 * Real.log (Real.log (n : ℝ) +
                (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))))) ≤
            2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
          (div_le_iff₀ h2log).mpr (by linarith)
        have hmul : (Real.log (n : ℝ) +
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) *
            (1 - 1 / (2 * Real.log (Real.log (n : ℝ) +
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))))) =
            Real.log (n : ℝ) + (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) -
              (Real.log (n : ℝ) + (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) /
                (2 * Real.log (Real.log (n : ℝ) +
                  (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))))) := by
          ring
        have ht_def : Real.log (n : ℝ) +
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) -
              (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) =
            Real.log (n : ℝ) := by ring
        linarith
      have hchild := rosser_schoenfeld_theta_lower_analytic
        (Real.log (n : ℝ) + (2 + 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))))
        (by linarith)
      linarith
    · have h := div_nonneg (by positivity : (0 : ℝ) ≤ 0.9 * Real.log (n : ℝ)) hLpos.le
      linarith
    · have h := div_nonneg (by positivity : (0 : ℝ) ≤ 0.9 * Real.log (n : ℝ)) hLpos.le
      linarith

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (n : ℕ) (hn : 3 ≤ n) (hlog : 294 ≤ Real.log (n : ℝ)) :
    ∃ y : ℝ, 288 ≤ Real.log (n : ℝ) + y ∧
      Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y) ∧
      0 ≤ y - 2 ∧ y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
  TaoFivePrimes.solution n hn hlog
