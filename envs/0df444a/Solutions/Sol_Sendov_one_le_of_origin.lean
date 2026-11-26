-- Prove2me | solution 1 for Sendov.one_le_of_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:50.218818+00:00
-- url     : https://prove2.me/submissions/0894b55f-0122-473f-b145-63585de516ed

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified
import Theorems.Thm_Sendov_integral_beta_split
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_QQ_nonneg
import Theorems.Thm_Sendov_QQ_one
import Theorems.Thm_Sendov_mul_eq_c


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hB1lt : QQ (a * x) (a ^ 2) 1 < 1)
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (0 : ℝ) < M n := M_pos hn2
  have hMn : M n = (n : ℝ) - 1 := rfl
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1def
  set I3 : ℝ := ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) with hI3def
  -- `1 - β(1) = 2ax - a²`, so `β(1) < 1` gives `ax > 0`
  have hB1eq : B1 = 1 - 2 * (a * x) + a ^ 2 := by rw [hB1def, QQ_one]
  have hax : 0 < a * x := by nlinarith [sq_nonneg a]
  have hxpos : 0 < x := by nlinarith [hax, ha]
  -- `x² ≥ 1 - β(1)`, which is `(x-a)² ≥ 0`
  have hxsq : 1 - B1 ≤ x ^ 2 := by rw [hB1eq]; nlinarith [sq_nonneg (x - a)]
  have hx2pos : (0 : ℝ) < x ^ 2 := by positivity
  have hinv : 1 / x ^ 2 ≤ 1 / (1 - B1) := by
    apply one_div_le_one_div_of_le (by linarith) hxsq
  have hone_sub : 1 - x ^ 2 ≤ B1 := by linarith
  -- the integral bound
  have hsplit := integral_beta_split hn ha ha1 hx hax
  have hI3nn : (0 : ℝ) ≤ I3 := by
    rw [hI3def]
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    have hfe : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfe u) _)
  -- multiply the split by `a² n M` and simplify the Beta term to `1/x²`
  have hcoef : (0 : ℝ) ≤ a ^ 2 * n * M n := by positivity
  have hbeta_simp : a ^ 2 * (n : ℝ) * M n
      * (1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))) = 1 / x ^ 2 := by
    have hane : (a : ℝ) ≠ 0 := ha.ne'
    have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
    have hn1 : ((n : ℝ) - 1) ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    rw [hMn]
    field_simp
  have hkey : a ^ 2 * n * M n
        * (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / x ^ 2 + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3 := by
    refine (mul_le_mul_of_nonneg_left hsplit hcoef).trans_eq ?_
    rw [mul_add, hbeta_simp]
    congr 1
    ring
  -- assemble
  have hax_eq : a * x = 1 - B1 / 2 - α / M n := mul_eq_c hn2 hα
  have hmain : 2 * α ≤ B1 / (1 - B1) + B1 / 2 + α / M n + B1 / (2 * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    have hlast : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3
        ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
      have hc : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) / 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
        positivity
      nlinarith [mul_nonneg (mul_nonneg hc (sub_nonneg.2 hone_sub)) hI3nn]
    have hfirst : (1 - x ^ 2) / (2 * M n) ≤ B1 / (2 * M n) := by
      apply div_le_div_of_nonneg_right hone_sub (by positivity)
    have hne1 : (1 : ℝ) - B1 ≠ 0 := by linarith
    have hrec : 1 / (1 - B1) = 1 + B1 / (1 - B1) := by
      field_simp
      ring
    have hinv' : 1 / x ^ 2 ≤ 1 + B1 / (1 - B1) := by rw [← hrec]; exact hinv
    -- do NOT rewrite `hax_eq` into `horigin`: it would also rewrite the `a * x` inside the
    -- integral, and the resulting atom would no longer match `hkey`
    linarith [horigin, hkey, hinv', hfirst, hlast, hax_eq]
  -- divide by `2α`
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hne : (1 : ℝ) - B1 ≠ 0 := by linarith
  have h1 : 2 * α * (B1 / (2 * α * (1 - B1))) = B1 / (1 - B1) := by
    field_simp
  have h2 : 2 * α * (B1 / (4 * α)) = B1 / 2 := by
    field_simp
    ring
  have h3 : 2 * α * (1 / (2 * M n)) = α / M n := by
    field_simp
  have h4 : 2 * α * (B1 / (4 * α * M n)) = B1 / (2 * M n) := by
    field_simp
    ring
  have h5 : 2 * α * ((a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / (4 * α) * I3)
      = (a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    field_simp
    ring
  refine le_of_mul_le_mul_left ?_ h2α
  rw [mul_one, mul_add, mul_add, mul_add, mul_add, h1, h2, h3, h4, h5]
  exact hmain
end Sendov
