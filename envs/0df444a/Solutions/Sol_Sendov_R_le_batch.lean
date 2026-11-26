-- Prove2me | solution 1 for Sendov.R_le_batch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:09.59358+00:00
-- url     : https://prove2.me/submissions/b048a538-7e46-41d0-a66c-2a369da6bfaf

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
import Theorems.Thm_Sendov_M_mono
import Theorems.Thm_Sendov_A_mono
import Theorems.Thm_Sendov_integral_anti
import Theorems.Thm_Sendov_A_nonneg
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_Q_nonneg
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
variable {α t : ℝ}
open MeasureTheory
namespace Sendov
theorem _root_.solution {n₀ n n₁ : ℕ} (h0 : 5 ≤ n₀) (h1 : n₀ ≤ n) (h2 : n ≤ n₁) (hα : 0 ≤ α)
    (hc0 : 0 ≤ c n₀ α) (hfn : c n α ^ 2 ≤ A n α) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n₀) + 1 / (4 * M n₀ * (3 + α))
      + A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n₀ α t ^ (((n₀ : ℝ) - 4) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have h02 : 2 ≤ n₀ := by omega
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hM0 : 0 < M n₀ := M_pos h02
  have hMn : 0 < M n := M_pos hn2
  have hMn1 : 0 < M n₁ := lt_of_lt_of_le hMn (M_mono h2)
  -- the elementary part decreases
  have hbase : 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      ≤ 1 / (2 * M n₀) + 1 / (4 * M n₀ * (3 + α)) := by
    have hMM : M n₀ ≤ M n := M_mono h1
    have e1 : 1 / (2 * M n) ≤ 1 / (2 * M n₀) := by
      apply one_div_le_one_div_of_le (by linarith); linarith
    have e2 : 1 / (4 * M n * (3 + α)) ≤ 1 / (4 * M n₀ * (3 + α)) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith
  -- the prefactor increases
  have hAn : 0 ≤ A n α := A_nonneg hfn
  have hApre : A n α ≤ A n₁ α := A_mono hn2 h2 hα
  have hnn1 : (n : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast h2
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn12 : (2 : ℝ) ≤ (n₁ : ℝ) := le_trans hn2R hnn1
  have hA2 : A n α ^ 2 ≤ A n₁ α ^ 2 := by nlinarith [hAn, hApre]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hMle : M n ≤ M n₁ := M_mono h2
  have hA1nn : (0 : ℝ) ≤ A n₁ α ^ 2 := sq_nonneg _
  have e1 : A n α ^ 2 * n ≤ A n₁ α ^ 2 * n₁ := mul_le_mul hA2 hnn1 hnn hA1nn
  have e2 : A n α ^ 2 * n * M n ≤ A n₁ α ^ 2 * n₁ * M n₁ :=
    mul_le_mul e1 hMle hMn.le (by positivity)
  have e3 : A n α ^ 2 * n * M n * ((n : ℝ) - 2) ≤ A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) :=
    mul_le_mul e2 (by linarith) (by linarith) (by positivity)
  have hc : (0 : ℝ) < 4 * (3 + α) := by positivity
  have hpref : A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
      ≤ A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α)) := by
    rw [div_le_div_iff_of_pos_right hc]
    exact e3
  -- the moment decreases
  have hI := integral_anti (m := n₀) (n := n) h0 h1 hα hc0 hfn
  have hInn : 0 ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (Q_nonneg hfn u) _)
  have hprefnn : 0 ≤ A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α)) := by
    have h4 : (0 : ℝ) ≤ (n₁ : ℝ) - 2 := by linarith
    have h5 : (0 : ℝ) ≤ M n₁ := hMn1.le
    positivity
  rw [R]
  nlinarith [hbase, hpref, hI, hInn, hprefnn]
end Sendov
