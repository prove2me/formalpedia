-- Prove2me | solution 1 for Sendov.integral_beta_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:27.273655+00:00
-- url     : https://prove2.me/submissions/3fb7e94f-e584-4981-9424-9c39a8d56185

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified
import Theorems.Thm_Sendov_beta_split
import Theorems.Thm_Sendov_QQ_nonneg
import Theorems.Thm_Sendov_continuous_pow_mul_QQ
import Theorems.Thm_Sendov_continuous_rpow_const
import Theorems.Thm_Sendov_integral_chord_lin


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hax : 0 < a * x) :
    (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
          * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hr2 : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hr4 : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by linarith
  have haxle : a * x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), ha.le]
  -- the three continuous integrands
  have hc1 : Continuous fun t : ℝ => t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    simpa using continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hr2
  have hc2 : Continuous fun t : ℝ => t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
    (by fun_prop : Continuous fun t : ℝ => t).mul
      ((continuous_rpow_const hs.le).comp (by fun_prop))
  have hc3 : Continuous fun t : ℝ =>
      ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
        * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
    (continuous_pow_mul_QQ (a * x) (a ^ 2) 3 hr4).const_mul _
  -- integrate the pointwise bound
  have hstep : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + ∫ t in (0 : ℝ)..1, ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
            * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) := by
    rw [← intervalIntegral.integral_add (hc2.intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable _ _)
      ((hc2.add hc3).intervalIntegrable _ _) ?_
    intro u hu
    have h := beta_split hn ha ha1 hx hu.1 hu.2
    have hu0 : (0 : ℝ) ≤ u := hu.1
    nlinarith [h, hu0, Real.rpow_nonneg (QQ_nonneg (by nlinarith [sq_nonneg a] :
      (a * x) ^ 2 ≤ a ^ 2) u) (((n : ℝ) - 4) / 2)]
  refine hstep.trans ?_
  rw [intervalIntegral.integral_const_mul]
  gcongr
  -- the chord piece: enlarge to `[0, 1/(ax)]` and evaluate
  have hrest : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
      ≤ ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    have hone : (1 : ℝ) ≤ 1 / (a * x) := by rw [le_div_iff₀ hax]; linarith
    have hadd : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + (∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        = ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hc2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
    have hnn : (0 : ℝ) ≤ ∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
      refine intervalIntegral.integral_nonneg hone ?_
      intro u hu
      have : (0 : ℝ) ≤ 1 - a * x * u := by
        have := hu.2
        rw [le_div_iff₀ hax] at this
        linarith
      exact mul_nonneg (by linarith [hu.1]) (Real.rpow_nonneg this _)
    linarith
  refine hrest.trans_eq ?_
  rw [integral_chord_lin hs hax]
  congr 1
  ring
end Sendov
