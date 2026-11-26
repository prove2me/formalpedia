-- Prove2me | solution 1 for Sendov.origin_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:40.857839+00:00
-- url     : https://prove2.me/submissions/348a136a-0b01-4142-a721-4c79155d00f4

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_grow
import Theorems.Thm_Sendov_collapse_J
import Theorems.Thm_Sendov_norm_Worigin_le
import Theorems.Thm_Sendov_xy_bounds
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_Jsum_estimate
import Theorems.Thm_Sendov_norm_prod_le_one
import Theorems.Thm_Sendov_one_le_tri
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.Fprod_zero
attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 5 ≤ n) {a x y α : ℝ} {z q : Multiset ℂ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I))
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hfirst : (n : ℂ) * ∫ t in (0 : ℝ)..1, Fprod a q t = (-1) ^ (n - 1) * q.prod * z.prod)
    (hsecond : (n : ℂ) * (q.map (fun v => 1 - (a : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z))
    (hα : α = M n * (1 - a ^ 2) / 2) :
    2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hxre, hx2⟩ := xy_bounds hn2 hqcard hq1 hxy
  have hxle : x ≤ 1 := by nlinarith [hx2, sq_nonneg y]
  -- the triangle inequality `(tri)` and the defect estimate
  have htri := one_le_tri hn2 hqcard hq0 hq1 (le_of_lt ha0) hxre hxy
  have hJ := Jsum_estimate (n := n) hn2 (a := a) (x := x) (y := y) hqcard hz1 hq1 hcent hxy
  -- `(f1aq)`
  have hF1 : Fprod a q 1 = (q.map (fun v => 1 - (a : ℂ) * v)).prod := by
    simp only [Fprod, Complex.ofReal_one, mul_one]
  have hsecond' : (n : ℂ) * Fprod a q 1
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z) := by
    rw [hF1]; exact hsecond
  have hf1aq : (n : ℂ) * (Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t)
      = (-1) ^ (n - 1) * ((q.prod * z.prod) * Worigin n a x y
        + (a : ℂ) * (q.prod * sumEraseProd z
            - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * I))
              * (q.prod * z.prod))) := by
    simp only [Worigin]
    linear_combination hsecond' + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * hfirst
  -- `(tri-2)`
  have hsign : ‖((-1 : ℂ)) ^ (n - 1)‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  have hana : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ha0)]
  have hPJ0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
  have hPJ1 : ‖q.prod‖ * ‖z.prod‖ ≤ 1 := by
    have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
    have h2 : ‖z.prod‖ ≤ 1 := norm_prod_le_one z hz1
    nlinarith [norm_nonneg q.prod, norm_nonneg z.prod]
  have hstep1 : (n : ℝ) * ‖Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t‖
      ≤ ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
        + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
    have h := congrArg norm hf1aq
    rw [norm_mul, hnn, norm_mul, hsign, one_mul] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, hana]
    have hmul := mul_le_mul_of_nonneg_left hJ (le_of_lt ha0)
    linarith [hmul]
  -- `(grow)` collapses `|J|` to `1`, giving `(tri-3)`
  have hgrow := grow (n := n) hn (a := a) (x := x) (y := y) ha0 hxle
  have hcoll : ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
      + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2)
      ≤ ‖Worigin n a x y‖ := by
    have hc : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) ≤ ‖Worigin n a x y‖ := by
      have he : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) = 2 * a * (n : ℝ) / ((n : ℝ) - 1) := by ring
      rw [he]; exact hgrow
    have hcnn : (0 : ℝ) ≤ a * ((n : ℝ) / ((n : ℝ) - 1)) := by positivity
    exact collapse_J hPJ1 hcnn hc
  have htri3 : (n : ℝ) ≤ ‖Worigin n a x y‖
      + (n : ℝ) * (a ^ 2 * ((n : ℝ) - 1)
        * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    have h := mul_le_mul_of_nonneg_left htri (le_of_lt hnpos)
    linarith [h, hstep1, hcoll]
  -- eliminate `y`, and assemble
  have hWle := norm_Worigin_le (n := n) (y := y) ha0 ha1 hn1 hxle (by linarith [hx2])
  simp only [M] at hα ⊢
  linarith [htri3, hWle, hα]
end Sendov
