-- Prove2me | solution 1 for Sendov.alpha_le_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:53.586315+00:00
-- url     : https://prove2.me/submissions/2121a4be-dbd4-4fb9-a59f-182e3d8f0718

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17
import Theorems.Thm_Sendov_log_le_div_exp_one
import Theorems.Thm_Sendov_exp_le_one_div_one_sub
import Theorems.Thm_Sendov_log_seventeen_ge
import Theorems.Thm_Sendov_tail_poly_bound
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_QQ_nonneg
import Theorems.Thm_Sendov_QQ_one
import Theorems.Thm_Sendov_alpha_le_half
import Theorems.Thm_Sendov_integral_le_tail_lin


set_option autoImplicit false
open Sendov
open MeasureTheory Real
set_option maxHeartbeats 1000000
namespace Sendov
theorem _root_.solution {n : ℕ} {a x α : ℝ} (hn : 5 ≤ n)
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    α ≤ 17 := by
  by_contra hcon
  rw [not_le] at hcon
  have hn2 : 2 ≤ n := by omega
  have hM : (0 : ℝ) < M n := M_pos hn2
  have hα0 : (0 : ℝ) < α := by linarith
  -- feasibility forces `n - 1 ≥ 2α > 34`
  have hMge : 2 * α ≤ M n := by linarith [alpha_le_half hn2 hα]
  have hM34 : (34 : ℝ) < M n := by linarith
  have hMn : M n = (n : ℝ) - 1 := rfl
  -- the standing facts about `β(1)`
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1def
  set r : ℝ := ((n : ℝ) - 2) / 2 with hrdef
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ B1 := QQ_nonneg hfeas 1
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hB1lt : B1 < 1 := by
    have : α / (3 + α) < 1 := by rw [div_lt_one h3]; linarith
    linarith
  have hB1eq : B1 = 1 - 2 * (a * x) + a ^ 2 := by rw [hB1def, QQ_one]
  have hax : 0 < a * x := by nlinarith [sq_nonneg a]
  have haxle : a * x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), ha.le]
  have hxpos : 0 < x := by nlinarith [hax, ha]
  have hr : (0 : ℝ) < r := by rw [hrdef]; rw [hMn] at hM34; linarith
  -- `log α ≥ 2.83`
  have hlog17 : (2.83 : ℝ) ≤ Real.log α :=
    le_trans log_seventeen_ge (Real.log_le_log (by norm_num) hcon.le)
  have hlogpos : (0 : ℝ) < Real.log α := by linarith
  -- `x² ≥ 1 - β(1) ≥ log α / α`
  have hxsq : Real.log α / α ≤ x ^ 2 := by
    have h1 : 1 - B1 ≤ x ^ 2 := by rw [hB1eq]; nlinarith [sq_nonneg (x - a)]
    rw [div_le_iff₀ hα0]
    nlinarith [hlogb, h1]
  -- the chord split of the integral
  have hI1 := integral_le_tail_lin hfeas hax haxle hr
  set I1 : ℝ := ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ r with hI1def
  have hprod : (r + 1) * (r + 2) = (n : ℝ) * ((n : ℝ) + 2) / 4 := by rw [hrdef]; ring
  have hane : (a : ℝ) ≠ 0 := ha.ne'
  have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hMn] at hM34; linarith
  have hbeta_term : a ^ 2 * n * M n * (1 / ((a * x) ^ 2 * ((r + 1) * (r + 2))))
      = 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) := by
    rw [hprod]
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hn2' : (n : ℝ) + 2 ≠ 0 := by linarith
    field_simp
  have hcoefnn : (0 : ℝ) ≤ a ^ 2 * n * M n := by positivity
  have hstep : a ^ 2 * n * M n * I1
      ≤ 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) + a ^ 2 * n * M n * (B1 ^ r / 2) := by
    calc a ^ 2 * n * M n * I1
        ≤ a ^ 2 * n * M n * (1 / ((a * x) ^ 2 * ((r + 1) * (r + 2))) + B1 ^ r / 2) :=
          mul_le_mul_of_nonneg_left hI1 hcoefnn
      _ = 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) + a ^ 2 * n * M n * (B1 ^ r / 2) := by
          rw [mul_add, hbeta_term]
  -- `4M/(x²(n+2)) ≤ 4/x² ≤ 4α/log α`
  have hfourx : 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) ≤ 4 * α / Real.log α := by
    have h1 : 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) ≤ 4 / x ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : M n ≤ (n : ℝ) + 2 := by rw [hMn]; linarith
      nlinarith [sq_nonneg x, hxpos]
    have h2 : (4 : ℝ) / x ^ 2 ≤ 4 * α / Real.log α := by
      rw [div_le_div_iff₀ (by positivity) hlogpos]
      have := hxsq
      rw [div_le_iff₀ hα0] at this
      nlinarith [this]
    linarith
  have hfirst : (1 - x ^ 2) / (2 * M n) ≤ 1 / (2 * M n) := by
    have hD : (0 : ℝ) < 2 * M n := by linarith
    rw [div_le_div_iff₀ hD hD]
    nlinarith [sq_nonneg x, hD]
  have hmain : 2 * α ≤ 1 / (2 * M n) + 4 * α / Real.log α + a ^ 2 * n * M n * (B1 ^ r / 2) := by
    linarith [horigin, hstep, hfourx, hfirst, hax]
  -- the substitution `v = M/(2α) - 1`
  -- `obtain` rather than `set`: a `set` binding is a local *definition*, which `linarith`
  -- zeta-reduces back into `M n / (2 * α) - 1`, making its goals nonlinear in `α`
  obtain ⟨v, hvdef⟩ : ∃ w : ℝ, w = M n / (2 * α) - 1 := ⟨_, rfl⟩
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hv0 : 0 ≤ v := by
    rw [hvdef, sub_nonneg, le_div_iff₀ h2α]
    linarith
  have hMv : M n = 2 * α * (v + 1) := by
    rw [hvdef]
    field_simp
    ring
  have ha2 : a ^ 2 = 1 - 2 * α / M n := by
    rw [hα]
    field_simp
    ring
  have hav : a ^ 2 * M n / (2 * α) = v := by
    rw [ha2, hvdef]
    field_simp
  -- `β(1) ≤ exp(-log α/α)`, hence `β(1)^r ≤ exp(-(v+1)log α) exp(log α/(2α))`
  have hB1exp : B1 ≤ exp (-(Real.log α / α)) := by
    have h1 : B1 ≤ exp (B1 - 1) := by linarith [Real.add_one_le_exp (B1 - 1)]
    refine h1.trans (Real.exp_le_exp.2 ?_)
    have : Real.log α / α ≤ 1 - B1 := by rw [div_le_iff₀ hα0]; linarith
    linarith
  have hrM : r = (M n - 1) / 2 := by rw [hrdef, hMn]; ring
  have hB1r : B1 ^ r ≤ exp (-(v * Real.log α)) / α * exp (Real.log α / (2 * α)) := by
    have h1 : B1 ^ r ≤ exp (-(Real.log α / α) * r) := by
      calc B1 ^ r ≤ exp (-(Real.log α / α)) ^ r := Real.rpow_le_rpow hB0 hB1exp hr.le
        _ = exp (-(Real.log α / α) * r) := by rw [← Real.exp_mul]
    refine h1.trans_eq ?_
    have hexpo : -(Real.log α / α) * r
        = (-(v * Real.log α) + -Real.log α) + Real.log α / (2 * α) := by
      rw [hrM, hMv]
      field_simp
      ring
    have hinv : exp (-Real.log α) = 1 / α := by
      rw [Real.exp_neg, Real.exp_log hα0]
      ring
    rw [hexpo, Real.exp_add, Real.exp_add, hinv]
    ring
  -- the two exponential factors
  have hvexp : exp (-(v * Real.log α)) ≤ exp (-(2.83 * v)) :=
    Real.exp_le_exp.2 (by nlinarith [hv0, hlog17])
  have he1 : (2.7 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hsecexp : exp (Real.log α / (2 * α)) ≤ 1 / (1 - 0.1852) := by
    refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_one_div_one_sub (by norm_num))
    have h := log_le_div_exp_one hα0
    have h27 : α / exp 1 ≤ α / 2.7 :=
      div_le_div_of_nonneg_left hα0.le (by norm_num) he1.le
    rw [div_le_iff₀ h2α]
    have hlast : α / 2.7 ≤ 0.1852 * (2 * α) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2.7)]
      nlinarith [hα0]
    linarith [h, h27, hlast]
  -- assemble the geometric term
  have hnv : (n : ℝ) = 2 * α * (v + 1) + 1 := by
    rw [← hMv, hMn]
    ring
  have hthird : a ^ 2 * n * M n * (B1 ^ r / 2) ≤ 0.50543 * α := by
    have hexpnn : (0 : ℝ) ≤ exp (-(2.83 * v)) := (Real.exp_pos _).le
    have hkey : a ^ 2 * n * M n * (B1 ^ r / 2) = (n : ℝ) * α * v * B1 ^ r := by
      rw [← hav]
      field_simp
    rw [hkey]
    have hstep1 : (n : ℝ) * α * v * B1 ^ r
        ≤ (n : ℝ) * α * v * (exp (-(2.83 * v)) / α * (1 / (1 - 0.1852))) := by
      refine mul_le_mul_of_nonneg_left (hB1r.trans ?_) (by positivity)
      refine mul_le_mul ?_ hsecexp (Real.exp_pos _).le (by positivity)
      gcongr
    refine hstep1.trans ?_
    have hfinal : (n : ℝ) * α * v * (exp (-(2.83 * v)) / α * (1 / (1 - 0.1852)))
        = α * (v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v))) * (1 / (1 - 0.1852)) := by
      rw [hnv]
      field_simp
    rw [hfinal]
    have hbound : v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v)) ≤ 0.4118 := by
      refine le_trans ?_ (tail_poly_bound hv0)
      have hinv : (1 : ℝ) / α ≤ 1 / 17 := by
        rw [div_le_div_iff₀ hα0 (by norm_num)]; linarith
      have hprod : (0 : ℝ) ≤ v * exp (-(2.83 * v)) := mul_nonneg hv0 hexpnn
      nlinarith [mul_le_mul_of_nonneg_left hinv hprod]
    have hscale : α * (v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v))) ≤ α * 0.4118 :=
      mul_le_mul_of_nonneg_left hbound hα0.le
    linarith [hscale]
  -- the numeric contradiction
  have hlogterm : 4 * α / Real.log α ≤ 1.41343 * α := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [hlog17, hα0]
  have hMterm : 1 / (2 * M n) ≤ 1 / 68 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith [hmain, hlogterm, hMterm, hthird, hcon]
end Sendov
