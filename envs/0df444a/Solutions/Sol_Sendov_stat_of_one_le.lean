-- Prove2me | solution 1 for Sendov.stat_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:36.942777+00:00
-- url     : https://prove2.me/submissions/26ab48df-8266-42fa-9eb5-212750560bda

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
import Theorems.Thm_Sendov_c_le_mul
import Theorems.Thm_Sendov_A_eq_sq
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_QQ_nonneg
import Theorems.Thm_Sendov_Q_eq_QQ
import Theorems.Thm_Sendov_integral_QQ_anti


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 5 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (h1le : 1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :
    1 ≤ R n α := by
  have hn2 : 2 ≤ n := by omega
  have hM : (0 : ℝ) < M n := M_pos hn2
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hA : A n α = a ^ 2 := A_eq_sq hn2 hα
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1
  -- the standing facts about `β(1)`
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ B1 := QQ_nonneg hfeas 1
  have hkey : B1 * (3 + α) ≤ α := by
    rw [← le_div_iff₀ h3]; exact hbeta
  have hB1lt : B1 < 1 := by nlinarith [hα0, hB0]
  -- the four elementary terms
  have t1 : B1 / (2 * α * (1 - B1)) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [hkey, hB0, hα0]
  have t2 : B1 / (4 * α) ≤ 1 / (4 * (3 + α)) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hkey]
  have t4 : B1 / (4 * α * M n) ≤ 1 / (4 * M n * (3 + α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hM]
  -- the integral term
  have hcle : c n α ≤ a * x := c_le_mul hn2 hα hα0 hbeta
  have hr : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hI : (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (c n α) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) :=
    integral_QQ_anti hcle hfeas hr 3
  have hInn : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfeas u) _)
  have hpre : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    positivity
  have t5 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2) := by
    have hcoef : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hkey, hpre]
    have hstep1 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
      mul_le_mul_of_nonneg_right hcoef hInn
    refine hstep1.trans ?_
    have hcnn : (0 : ℝ) ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA]; positivity
    refine mul_le_mul_of_nonneg_left ?_ hcnn
    simpa only [Q_eq_QQ, hA] using hI
  rw [R]
  linarith
end Sendov
