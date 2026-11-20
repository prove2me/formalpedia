-- Prove2me | solution 1 for RademacherGamma_p5_gauss_bounds
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:53:02.45628+00:00
-- url     : https://prove2.me/submissions/210c4c8b-5dd5-4ae0-8bc0-aa12128ac999

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_RademacherGamma_p3_gauss_bounds

namespace SolGammaHelpers

open Real MeasureTheory Filter Set
open scoped Topology

private lemma P3_gauss_bounds (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) + 2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
      |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀| ≤
        (11 / 60) * (2 * δ) * t * √t :=
  RademacherGamma_p3_gauss_bounds a₀ δ t hδ ht

/-! ### Elementary exponential polynomial bounds -/

private lemma exp_ge_poly2 {x : ℝ} (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 3
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_ge_poly5 {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 6
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_ge_poly9 {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 +
      x ^ 7 / 5040 + x ^ 8 / 40320 + x ^ 9 / 362880 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 10
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_ge_poly3 {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_neg_le_one_sub {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2 - Real.exp (-t))
      (-(1 - y - Real.exp (-y))) y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2) (-1 + y) y := by
      have ha : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
        simpa using (hasDerivAt_const y (1 : ℝ)).fun_sub (hasDerivAt_id y)
      have hb : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
        simpa using (hasDerivAt_pow 2 y).div_const 2
      exact ha.fun_add hb
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-y)) y := by
      simpa using (hasDerivAt_id y).neg.exp
    exact h1.fun_sub h2 |>.congr_deriv (by ring)
  have hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ -(1 - y - Real.exp (-y)) := by
    intro y hy
    have := Real.one_sub_le_exp_neg y
    linarith
  have hmono : (fun t : ℝ => 1 - t + t ^ 2 / 2 - Real.exp (-t)) 0 ≤
      (fun t : ℝ => 1 - t + t ^ 2 / 2 - Real.exp (-t)) x :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy
        rw [(hderiv y).deriv]
        exact hnonneg y hy.le)
      (by simp) hx hx
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, neg_zero, Real.exp_zero, sub_self] at hmono
  linarith

private lemma exp_neg_ge_poly1 {x : ℝ} : 1 - x ≤ Real.exp (-x) :=
  Real.one_sub_le_exp_neg x

private lemma exp_neg_ge_poly3 {x : ℝ} (hx : 0 ≤ x) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 ≤ Real.exp (-x) := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6))
      ((1 - y + y ^ 2 / 2) - Real.exp (-y)) y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-y)) y := by
      simpa using (hasDerivAt_id y).neg.exp
    have ha : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
      simpa using (hasDerivAt_const y (1 : ℝ)).fun_sub (hasDerivAt_id y)
    have hb : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have hc : HasDerivAt (fun t : ℝ => t ^ 3 / 6) (y ^ 2 / 2) y :=
      ((hasDerivAt_pow 3 y).div_const 6).congr_deriv (by ring)
    have h2 : HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2 - t ^ 3 / 6) (-1 + y - y ^ 2 / 2) y :=
      (ha.fun_add hb).fun_sub hc
    exact h1.fun_sub h2 |>.congr_deriv (by ring)
  have hmono : (fun t : ℝ => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6)) 0 ≤
      (fun t : ℝ => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6)) x :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy
        rw [(hderiv y).deriv]
        have := exp_neg_le_one_sub hy.le
        linarith)
      (by simp) hx hx
  simp at hmono
  linarith

private lemma exp_ub_of_le {z c B : ℝ} (hc0 : 0 ≤ c) (hz : z ≤ c)
    (hB0 : 0 < B) (hpoly : 1 / B ≤ 1 - c + c ^ 2 / 2 - c ^ 3 / 6) :
    Real.exp z ≤ B := by
  have hp := exp_neg_ge_poly3 hc0
  have h1 : 1 / B ≤ Real.exp (-z) :=
    le_trans hpoly (le_trans hp (Real.exp_le_exp.mpr (neg_le_neg hz)))
  rw [← inv_inv (Real.exp z), ← Real.exp_neg]
  have hinv := inv_anti₀ (div_pos one_pos hB0) h1
  rwa [one_div, inv_inv] at hinv

private lemma exp_neg_ub_of_le {x c B : ℝ} (hc0 : 0 ≤ c) (hcx : c ≤ x)
    (hpoly_pos : 0 < 1 + c + c ^ 2 / 2 + c ^ 3 / 6)
    (hB : 1 / (1 + c + c ^ 2 / 2 + c ^ 3 / 6) ≤ B) :
    Real.exp (-x) ≤ B := by
  have hp := exp_ge_poly3 hc0
  rw [Real.exp_neg]
  have hinv := (inv_le_inv₀ (Real.exp_pos _) hpoly_pos).mpr (le_trans hp (Real.exp_le_exp.mpr hcx))
  rw [one_div] at hB
  exact le_trans hinv hB

private lemma one_sub_exp_neg_ge {u : ℝ} (hu : 0 ≤ u) :
    (u + u ^ 2 / 2) / (1 + u + u ^ 2 / 2) ≤ 1 - Real.exp (-u) := by
  have hexp : 1 + u + u ^ 2 / 2 ≤ Real.exp u := exp_ge_poly2 hu
  have hpos : 0 < 1 + u + u ^ 2 / 2 := by positivity
  have hinv : Real.exp (-u) ≤ 1 / (1 + u + u ^ 2 / 2) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hpos hexp
  have h1 : 1 - 1 / (1 + u + u ^ 2 / 2) = (u + u ^ 2 / 2) / (1 + u + u ^ 2 / 2) := by
    field_simp
    ring
  linarith

private lemma one_sub_exp_neg_le_half {u : ℝ} (hu : 0 ≤ u) :
    1 - Real.exp (-u) ≤ u / (1 + u / 2) := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => (1 + t / 2) * Real.exp (-t) + t / 2 - 1)
      ((1 - (1 + y) * Real.exp (-y)) / 2) y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => 1 + t / 2) (1 / 2) y := by
      have hd : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) y := by
        simpa using (hasDerivAt_id y).div_const 2
      simpa using (hasDerivAt_const y (1 : ℝ)).fun_add hd
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-y)) y := by
      simpa using (hasDerivAt_id y).neg.exp
    have h12 : HasDerivAt (fun t : ℝ => (1 + t / 2) * Real.exp (-t) + t / 2)
        ((1 / 2) * Real.exp (-y) + (1 + y / 2) * (-Real.exp (-y)) + 1 / 2) y :=
      (h1.fun_mul h2).fun_add (by simpa using (hasDerivAt_id y).div_const 2)
    have hsub := h12.fun_sub (hasDerivAt_const y (1 : ℝ))
    simpa [sub_zero] using hsub.congr_deriv (by ring)
  have hmono : (fun t : ℝ => (1 + t / 2) * Real.exp (-t) + t / 2 - 1) 0 ≤
      (fun t : ℝ => (1 + t / 2) * Real.exp (-t) + t / 2 - 1) u :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy
        rw [(hderiv y).deriv]
        have hle : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
        have hmul : (1 + y) * Real.exp (-y) ≤ 1 := by
          rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos y)]
          exact hle
        linarith)
      (by simp) hu hu
  simp only [zero_div, add_zero, one_mul, neg_zero, Real.exp_zero, sub_self] at hmono
  have hden : 0 < 1 + u / 2 := by positivity
  rw [le_div_iff₀ hden]
  linarith

/-! ### P3 Euler-Maclaurin identity and Gaussian bound -/

private noncomputable def P3 (r : ℝ) : ℝ :=
  if 0 ≤ r then -(r / 12 - r ^ 2 / 4 + r ^ 3 / 6) else -(r / 12 + r ^ 2 / 4 + r ^ 3 / 6)

private lemma continuous_P3 : Continuous P3 := by
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_const continuous_id ?_
  intro x hx
  have hx0 : x = 0 := hx.symm
  subst hx0
  norm_num

private lemma abs_P3_le {r : ℝ} (hr1 : -1 / 2 ≤ r) (hr2 : r ≤ 1 / 2) :
    |P3 r| ≤ 1 / 124 := by
  have poly_ineq : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → u * (1 / 4 - u ^ 2) ≤ 3 / 62 := by
    intro u hu0 hu1
    have hnonneg : 0 ≤ u * (1 / 4 - u ^ 2) := by
      have : 0 ≤ 1 / 4 - u ^ 2 := by nlinarith
      exact mul_nonneg hu0 this
    have hsq : 432 * (u * (1 / 4 - u ^ 2)) ^ 2 ≤ 1 := by
      have hdiff : 4 - 4 * 432 * (u * (1 / 4 - u ^ 2)) ^ 2 =
          (12 * u ^ 2 - 1) ^ 2 * (4 - 12 * u ^ 2) := by ring
      have hp : 0 ≤ (12 * u ^ 2 - 1) ^ 2 * (4 - 12 * u ^ 2) := by
        have : 0 ≤ 4 - 12 * u ^ 2 := by nlinarith
        positivity
      linarith
    have hsq2 : (u * (1 / 4 - u ^ 2)) ^ 2 ≤ (3 / 62 : ℝ) ^ 2 := by nlinarith
    nlinarith
  rw [abs_le]
  by_cases hr0 : 0 ≤ r
  · simp only [P3, hr0, ↓reduceIte]
    set u := 1 / 2 - r
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hu1 : u ≤ 1 / 2 := by dsimp [u]; linarith
    have hid : r / 12 - r ^ 2 / 4 + r ^ 3 / 6 = u * (1 / 4 - u ^ 2) / 6 := by
      dsimp [u]; ring
    have hle := poly_ineq u hu0 hu1
    have hge : 0 ≤ u * (1 / 4 - u ^ 2) := mul_nonneg hu0 (by nlinarith)
    constructor <;> linarith
  · simp only [P3, hr0, ↓reduceIte]
    set u := 1 / 2 + r
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hu1 : u ≤ 1 / 2 := by dsimp [u]; linarith
    have hid : -(r / 12 + r ^ 2 / 4 + r ^ 3 / 6) = u * (1 / 4 - u ^ 2) / 6 := by
      dsimp [u]; ring
    have hle := poly_ineq u hu0 hu1
    have hge : 0 ≤ u * (1 / 4 - u ^ 2) := mul_nonneg hu0 (by nlinarith)
    constructor <;> linarith

private lemma P3_cell_identity (h h' h'' h''' : ℝ → ℝ) (a : ℝ)
    (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh' : ∀ x, HasDerivAt h' (h'' x) x)
    (hh'' : ∀ x, HasDerivAt h'' (h''' x) x)
    (hc''' : Continuous h''') :
    h a - ∫ w in (a - 1 / 2)..(a + 1 / 2), h w =
      (1 / 24) * (h' (a - 1 / 2) - h' (a + 1 / 2)) -
        ((∫ r in (-1 / 2 : ℝ)..0, P3 r * h''' (a + r)) +
          (∫ r in (0 : ℝ)..(1 / 2), P3 r * h''' (a + r))) := by
  have hc0 : Continuous h := continuous_iff_continuousAt.mpr fun x => (hh x).continuousAt
  have hc1 : Continuous h' := continuous_iff_continuousAt.mpr fun x => (hh' x).continuousAt
  have hc2 : Continuous h'' := continuous_iff_continuousAt.mpr fun x => (hh'' x).continuousAt
  -- Right half [0, 1/2]
  let pR : ℝ → ℝ := fun r => -(r / 12 - r ^ 2 / 4 + r ^ 3 / 6)
  let pR' : ℝ → ℝ := fun r => 1 / 24 - (1 / 2 - r) ^ 2 / 2
  let pR'' : ℝ → ℝ := fun r => 1 / 2 - r
  have hpR : ∀ r, HasDerivAt pR (pR' r) r := by
    intro r
    have h1 : HasDerivAt (fun x : ℝ => x / 12) (1 / 12) r := by
      simpa using (hasDerivAt_id r).div_const 12
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (r / 2) r :=
      ((hasDerivAt_pow 2 r).div_const 4).congr_deriv (by ring)
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (r ^ 2 / 2) r :=
      ((hasDerivAt_pow 3 r).div_const 6).congr_deriv (by ring)
    exact ((h1.fun_sub h2).fun_add h3).fun_neg.congr_deriv (by dsimp [pR']; ring)
  have hpR' : ∀ r, HasDerivAt pR' (pR'' r) r := by
    intro r
    have hsub : HasDerivAt (fun x : ℝ => 1 / 2 - x) (-1) r := by
      simpa using (hasDerivAt_const r (1 / 2 : ℝ)).fun_sub (hasDerivAt_id r)
    exact ((hasDerivAt_const r (1 / 24 : ℝ)).fun_sub ((hsub.pow 2).div_const 2)).congr_deriv
      (by dsimp [pR'']; ring)
  have hpR'' : ∀ r, HasDerivAt pR'' (-1) r := by
    intro r
    exact ((hasDerivAt_const r (1 / 2 : ℝ)).fun_sub (hasDerivAt_id r)).congr_deriv (by ring)
  have hR_eq : ∫ r in (0 : ℝ)..(1 / 2), P3 r * h''' (a + r) =
      ∫ r in (0 : ℝ)..(1 / 2), pR r * h''' (a + r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hr
    simp [P3, pR, hr.1]
  have hR1 : ∫ r in (0 : ℝ)..(1 / 2), pR r * h''' (a + r) =
      (pR (1 / 2) * h'' (a + 1 / 2) - pR 0 * h'' (a + 0)) -
        ∫ r in (0 : ℝ)..(1 / 2), pR' r * h'' (a + r) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun r _ => hpR r)
      (fun r _ => by simpa using (hh'' (a + r)).comp r ((hasDerivAt_id r).const_add a))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (hc'''.comp (continuous_const.add continuous_id)) _ _)
  have hR2 : ∫ r in (0 : ℝ)..(1 / 2), pR' r * h'' (a + r) =
      (pR' (1 / 2) * h' (a + 1 / 2) - pR' 0 * h' (a + 0)) -
        ∫ r in (0 : ℝ)..(1 / 2), pR'' r * h' (a + r) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun r _ => hpR' r)
      (fun r _ => by simpa using (hh' (a + r)).comp r ((hasDerivAt_id r).const_add a))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (hc2.comp (continuous_const.add continuous_id)) _ _)
  have hR3 : ∫ r in (0 : ℝ)..(1 / 2), pR'' r * h' (a + r) =
      (pR'' (1 / 2) * h (a + 1 / 2) - pR'' 0 * h (a + 0)) -
        ∫ r in (0 : ℝ)..(1 / 2), (-1 : ℝ) * h (a + r) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun r _ => hpR'' r)
      (fun r _ => by simpa using (hh (a + r)).comp r ((hasDerivAt_id r).const_add a))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (hc1.comp (continuous_const.add continuous_id)) _ _)
  -- Left half [-1/2, 0]
  let pL : ℝ → ℝ := fun r => -(r / 12 + r ^ 2 / 4 + r ^ 3 / 6)
  let pL' : ℝ → ℝ := fun r => 1 / 24 - (1 / 2 + r) ^ 2 / 2
  let pL'' : ℝ → ℝ := fun r => -(1 / 2 + r)
  have hpL : ∀ r, HasDerivAt pL (pL' r) r := by
    intro r
    have h1 : HasDerivAt (fun x : ℝ => x / 12) (1 / 12) r := by
      simpa using (hasDerivAt_id r).div_const 12
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (r / 2) r :=
      ((hasDerivAt_pow 2 r).div_const 4).congr_deriv (by ring)
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (r ^ 2 / 2) r :=
      ((hasDerivAt_pow 3 r).div_const 6).congr_deriv (by ring)
    exact ((h1.fun_add h2).fun_add h3).fun_neg.congr_deriv (by dsimp [pL']; ring)
  have hpL' : ∀ r, HasDerivAt pL' (pL'' r) r := by
    intro r
    have hadd : HasDerivAt (fun x : ℝ => 1 / 2 + x) 1 r := by
      simpa using (hasDerivAt_const r (1 / 2 : ℝ)).fun_add (hasDerivAt_id r)
    exact ((hasDerivAt_const r (1 / 24 : ℝ)).fun_sub ((hadd.pow 2).div_const 2)).congr_deriv
      (by dsimp [pL'']; ring)
  have hpL'' : ∀ r, HasDerivAt pL'' (-1) r := by
    intro r
    exact ((hasDerivAt_const r (1 / 2 : ℝ)).fun_add (hasDerivAt_id r)).fun_neg.congr_deriv (by ring)
  have hL_eq : ∫ r in (-1 / 2 : ℝ)..0, P3 r * h''' (a + r) =
      ∫ r in (-1 / 2 : ℝ)..0, pL r * h''' (a + r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hr
    rcases eq_or_lt_of_le hr.2 with rfl | hrlt
    · simp [P3, pL]
    · have hnot : ¬ (0 ≤ r) := not_le.mpr hrlt
      simp [P3, pL, hnot]
  have hL1 : ∫ r in (-1 / 2 : ℝ)..0, pL r * h''' (a + r) =
      (pL 0 * h'' (a + 0) - pL (-1 / 2) * h'' (a + (-1 / 2))) -
        ∫ r in (-1 / 2 : ℝ)..0, pL' r * h'' (a + r) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun r _ => hpL r)
      (fun r _ => by simpa using (hh'' (a + r)).comp r ((hasDerivAt_id r).const_add a))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (hc'''.comp (continuous_const.add continuous_id)) _ _)
  have hL2 : ∫ r in (-1 / 2 : ℝ)..0, pL' r * h'' (a + r) =
      (pL' 0 * h' (a + 0) - pL' (-1 / 2) * h' (a + (-1 / 2))) -
        ∫ r in (-1 / 2 : ℝ)..0, pL'' r * h' (a + r) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun r _ => hpL' r)
      (fun r _ => by simpa using (hh' (a + r)).comp r ((hasDerivAt_id r).const_add a))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (hc2.comp (continuous_const.add continuous_id)) _ _)
  have hL3 : ∫ r in (-1 / 2 : ℝ)..0, pL'' r * h' (a + r) =
      (pL'' 0 * h (a + 0) - pL'' (-1 / 2) * h (a + (-1 / 2))) -
        ∫ r in (-1 / 2 : ℝ)..0, (-1 : ℝ) * h (a + r) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun r _ => hpL'' r)
      (fun r _ => by simpa using (hh (a + r)).comp r ((hasDerivAt_id r).const_add a))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (hc1.comp (continuous_const.add continuous_id)) _ _)
  -- Combine integrals of h
  have hint_shift : ∫ w in (a - 1 / 2)..(a + 1 / 2), h w =
      (∫ r in (-1 / 2 : ℝ)..0, h (a + r)) + (∫ r in (0 : ℝ)..(1 / 2), h (a + r)) := by
    have hc_shift : Continuous (fun r => h (a + r)) := hc0.comp (continuous_const.add continuous_id)
    have hsplit : ∫ r in (-1 / 2 : ℝ)..(1 / 2), h (a + r) =
        (∫ r in (-1 / 2 : ℝ)..0, h (a + r)) + (∫ r in (0 : ℝ)..(1 / 2), h (a + r)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hc_shift.intervalIntegrable _ _) (hc_shift.intervalIntegrable _ _)).symm
    rw [← hsplit]
    have hcomp := intervalIntegral.integral_comp_add_left h a (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    convert hcomp.symm using 2; ring
  -- Evaluate boundary values
  have hpR_vals : pR (1 / 2) = 0 ∧ pR 0 = 0 ∧ pR' (1 / 2) = 1 / 24 ∧ pR' 0 = -1 / 12 ∧
      pR'' (1 / 2) = 0 ∧ pR'' 0 = 1 / 2 := by
    dsimp [pR, pR', pR'']; norm_num
  have hpL_vals : pL 0 = 0 ∧ pL (-1 / 2) = 0 ∧ pL' 0 = -1 / 12 ∧ pL' (-1 / 2) = 1 / 24 ∧
      pL'' 0 = -1 / 2 ∧ pL'' (-1 / 2) = 0 := by
    dsimp [pL, pL', pL'']; norm_num
  simp only [intervalIntegral.integral_neg, neg_one_mul, add_zero] at hR1 hR2 hR3 hL1 hL2 hL3
  rw [hR_eq, hL_eq, hL1, hL2, hL3, hR1, hR2, hR3, hint_shift]
  rcases hpR_vals with ⟨hR_0, hR_1, hR_2, hR_3, hR_4, hR_5⟩
  rcases hpL_vals with ⟨hL_0, hL_1, hL_2, hL_3, hL_4, hL_5⟩
  rw [hR_0, hR_1, hR_2, hR_3, hR_4, hR_5, hL_0, hL_1, hL_2, hL_3, hL_4, hL_5]
  have ha_sub : a + (-1 / 2 : ℝ) = a - 1 / 2 := by ring
  rw [ha_sub]
  ring


/-! ### Fifth-order Euler-Maclaurin identity and Gaussian bound (P5) -/

private noncomputable def P4_t (r : ℝ) : ℝ :=
  if 0 ≤ r then 1 / 720 - r ^ 2 / 24 + r ^ 3 / 12 - r ^ 4 / 24
  else 1 / 720 - r ^ 2 / 24 - r ^ 3 / 12 - r ^ 4 / 24

private noncomputable def P5 (r : ℝ) : ℝ :=
  if 0 ≤ r then r / 720 - r ^ 3 / 72 + r ^ 4 / 48 - r ^ 5 / 120
  else r / 720 - r ^ 3 / 72 - r ^ 4 / 48 - r ^ 5 / 120

private lemma continuous_P5 : Continuous P5 := by
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_const continuous_id ?_
  intro x hx
  have hx0 : x = 0 := hx.symm
  subst hx0
  norm_num

private lemma abs_P5_le {r : ℝ} (hr1 : -1 / 2 ≤ r) (hr2 : r ≤ 1 / 2) :
    |P5 r| ≤ 1 / 4800 := by
  let p5_pos : ℝ → ℝ := fun x => x / 720 - x ^ 3 / 72 + x ^ 4 / 48 - x ^ 5 / 120
  have hp5_deriv : ∀ x : ℝ, HasDerivAt p5_pos ((1 - 30 * (x * (1 - x)) ^ 2) / 720) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t / 720) (1 / 720) x := by
      simpa using (hasDerivAt_id x).div_const 720
    have h2 : HasDerivAt (fun t : ℝ => t ^ 3 / 72) (x ^ 2 / 24) x :=
      ((hasDerivAt_pow 3 x).div_const 72).congr_deriv (by ring)
    have h3 : HasDerivAt (fun t : ℝ => t ^ 4 / 48) (x ^ 3 / 12) x :=
      ((hasDerivAt_pow 4 x).div_const 48).congr_deriv (by ring)
    have h4 : HasDerivAt (fun t : ℝ => t ^ 5 / 120) (x ^ 4 / 24) x :=
      ((hasDerivAt_pow 5 x).div_const 120).congr_deriv (by ring)
    exact (((h1.fun_sub h2).fun_add h3).fun_sub h4).congr_deriv (by ring)
  have hp5_bounds : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → 0 ≤ p5_pos x ∧ p5_pos x ≤ 1 / 4800 := by
    intro x hx0 hx1
    constructor
    · have hfac : 720 * p5_pos x =
          x * (1 - 2 * x) * (7 / 6 - 6 * (x - 1 / 6) ^ 2 + 3 * x ^ 3) := by
        dsimp [p5_pos]; ring
      have h12 : 0 ≤ 1 - 2 * x := by linarith
      have hsq : (x - 1 / 6) ^ 2 ≤ 1 / 9 := by nlinarith only [hx0, hx1]
      have hx3 : 0 ≤ 3 * x ^ 3 := by positivity
      have hmid : 0 ≤ 7 / 6 - 6 * (x - 1 / 6) ^ 2 + 3 * x ^ 3 := by linarith only [hsq, hx3]
      have hprod : 0 ≤ 720 * p5_pos x := by
        rw [hfac]
        exact mul_nonneg (mul_nonneg hx0 h12) hmid
      linarith
    · by_cases h15 : x ≤ 1 / 5
      · have hcub : x / 720 - x ^ 3 / 72 ≤ 1 / 5760 := by
          have hid : x ^ 3 / 72 - x / 720 + 1 / 5760 =
              (x - 11 / 60) ^ 2 * (x + 11 / 30) / 72 + x / 86400 + 38 / 15552000 := by ring
          have hpos1 : 0 ≤ (x - 11 / 60) ^ 2 * (x + 11 / 30) / 72 := by
            have : 0 ≤ x + 11 / 30 := by linarith
            positivity
          linarith
        have hx4 : x ^ 4 / 48 ≤ (1 / 5 : ℝ) ^ 4 / 48 := by
          have : x ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 h15 4
          linarith
        have hx5 : 0 ≤ x ^ 5 / 120 := by positivity
        dsimp [p5_pos]; linarith
      · have hx_ge15 : 1 / 5 ≤ x := by linarith
        by_cases h1150 : x ≤ 11 / 50
        · have hmono : MonotoneOn (fun t : ℝ => (29 / 90000 : ℝ) * t - p5_pos t) (Set.Icc (1 / 5) (11 / 50)) := by
            apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
            · exact (Continuous.sub (continuous_const.mul continuous_id) (by dsimp [p5_pos]; fun_prop)).continuousOn
            · exact fun t _ => (((hasDerivAt_id t).const_mul (29 / 90000 : ℝ)).fun_sub (hp5_deriv t)).differentiableAt.differentiableWithinAt
            · intro t ht
              rw [interior_Icc] at ht
              have hder : HasDerivAt (fun s : ℝ => (29 / 90000 : ℝ) * s - p5_pos s)
                  (29 / 90000 - (1 - 30 * (t * (1 - t)) ^ 2) / 720) t :=
                (((hasDerivAt_id t).const_mul (29 / 90000 : ℝ)).congr_deriv (mul_one _)).fun_sub (hp5_deriv t)
              rw [hder.deriv]
              have hprod : 4 / 25 ≤ t * (1 - t) := by nlinarith only [ht.1, ht.2]
              have hprod_sq : (4 / 25 : ℝ) ^ 2 ≤ (t * (1 - t)) ^ 2 := by nlinarith only [hprod]
              linarith
          have hm := hmono ⟨le_rfl, by norm_num⟩ ⟨hx_ge15, h1150⟩ hx_ge15
          have hv : p5_pos (1 / 5) ≤ 198 / 1000000 := by dsimp [p5_pos]; norm_num
          dsimp only at hm
          linarith
        · have hx_ge1150 : 11 / 50 ≤ x := by linarith
          by_cases h14 : x ≤ 1 / 4
          · have hmono : MonotoneOn (fun t : ℝ => (165 / 1000000 : ℝ) * t - p5_pos t) (Set.Icc (11 / 50) (1 / 4)) := by
              apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
              · exact (Continuous.sub (continuous_const.mul continuous_id) (by dsimp [p5_pos]; fun_prop)).continuousOn
              · exact fun t _ => (((hasDerivAt_id t).const_mul (165 / 1000000 : ℝ)).fun_sub (hp5_deriv t)).differentiableAt.differentiableWithinAt
              · intro t ht
                rw [interior_Icc] at ht
                have hder : HasDerivAt (fun s : ℝ => (165 / 1000000 : ℝ) * s - p5_pos s)
                    (165 / 1000000 - (1 - 30 * (t * (1 - t)) ^ 2) / 720) t :=
                  (((hasDerivAt_id t).const_mul (165 / 1000000 : ℝ)).congr_deriv (mul_one _)).fun_sub (hp5_deriv t)
                rw [hder.deriv]
                have hprod : (11 / 50 : ℝ) * (39 / 50) ≤ t * (1 - t) := by nlinarith only [ht.1, ht.2]
                have hprod_sq : ((11 / 50 : ℝ) * (39 / 50)) ^ 2 ≤ (t * (1 - t)) ^ 2 := by nlinarith only [hprod]
                linarith
            have hm := hmono ⟨le_rfl, by norm_num⟩ ⟨hx_ge1150, h14⟩ hx_ge1150
            have hv : p5_pos (11 / 50) ≤ 203 / 1000000 := by dsimp [p5_pos]; norm_num
            dsimp only at hm
            linarith
          · have hx_ge14 : 1 / 4 ≤ x := by linarith
            have hant : AntitoneOn p5_pos (Set.Icc (1 / 4 : ℝ) (1 / 2)) := by
              apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
              · exact (by dsimp [p5_pos]; fun_prop : Continuous p5_pos).continuousOn
              · exact fun t _ => (hp5_deriv t).differentiableAt.differentiableWithinAt
              · intro t ht
                rw [interior_Icc] at ht
                rw [(hp5_deriv t).deriv]
                have hprod : 3 / 16 ≤ t * (1 - t) := by nlinarith only [ht.1, ht.2]
                have hprod_sq : (3 / 16 : ℝ) ^ 2 ≤ (t * (1 - t)) ^ 2 := by nlinarith only [hprod]
                linarith
            have hm := hant ⟨le_rfl, by norm_num⟩ ⟨hx_ge14, hx1⟩ hx_ge14
            have hv : p5_pos (1 / 4) ≤ 1 / 4800 := by dsimp [p5_pos]; norm_num
            linarith
  rw [abs_le]
  by_cases hr0 : 0 ≤ r
  · have hpos : P5 r = p5_pos r := by simp only [P5, hr0, ↓reduceIte, p5_pos]
    rw [hpos]
    have hb := hp5_bounds r hr0 hr2
    exact ⟨by linarith, hb.2⟩
  · have hneg : P5 r = -p5_pos (-r) := by
      simp only [P5, hr0, ↓reduceIte, p5_pos]
      ring
    rw [hneg]
    have hb := hp5_bounds (-r) (by linarith) (by linarith)
    exact ⟨by linarith, by linarith⟩

private lemma P5_cell_identity (h h' h'' h''' h4 h5 : ℝ → ℝ) (a : ℝ)
    (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh' : ∀ x, HasDerivAt h' (h'' x) x)
    (hh'' : ∀ x, HasDerivAt h'' (h''' x) x)
    (hh''' : ∀ x, HasDerivAt h''' (h4 x) x)
    (hh4 : ∀ x, HasDerivAt h4 (h5 x) x)
    (hc5 : Continuous h5) :
    h a - ∫ w in (a - 1 / 2)..(a + 1 / 2), h w =
      (1 / 24) * (h' (a - 1 / 2) - h' (a + 1 / 2)) -
        (7 / 5760) * (h''' (a - 1 / 2) - h''' (a + 1 / 2)) -
        ((∫ r in (-1 / 2 : ℝ)..0, P5 r * h5 (a + r)) +
          ∫ r in (0 : ℝ)..(1 / 2), P5 r * h5 (a + r)) := by
  have hc''' : Continuous h''' := continuous_iff_continuousAt.mpr fun x => (hh''' x).continuousAt
  have hc4 : Continuous h4 := continuous_iff_continuousAt.mpr fun x => (hh4 x).continuousAt
  have hp3 := P3_cell_identity h h' h'' h''' a hh hh' hh'' hc'''
  let p4R : ℝ → ℝ := fun r => 1 / 720 - r ^ 2 / 24 + r ^ 3 / 12 - r ^ 4 / 24
  let p4L : ℝ → ℝ := fun r => 1 / 720 - r ^ 2 / 24 - r ^ 3 / 12 - r ^ 4 / 24
  let p5R : ℝ → ℝ := fun r => r / 720 - r ^ 3 / 72 + r ^ 4 / 48 - r ^ 5 / 120
  let p5L : ℝ → ℝ := fun r => r / 720 - r ^ 3 / 72 - r ^ 4 / 48 - r ^ 5 / 120
  let p3R : ℝ → ℝ := fun r => -(r / 12 - r ^ 2 / 4 + r ^ 3 / 6)
  let p3L : ℝ → ℝ := fun r => -(r / 12 + r ^ 2 / 4 + r ^ 3 / 6)
  have hp4R : ∀ r, HasDerivAt p4R (p3R r) r := by
    intro r
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 24) (r / 12) r :=
      ((hasDerivAt_pow 2 r).div_const 24).congr_deriv (by ring)
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 12) (r ^ 2 / 4) r :=
      ((hasDerivAt_pow 3 r).div_const 12).congr_deriv (by ring)
    have h4 : HasDerivAt (fun x : ℝ => x ^ 4 / 24) (r ^ 3 / 6) r :=
      ((hasDerivAt_pow 4 r).div_const 24).congr_deriv (by ring)
    exact ((((hasDerivAt_const r (1 / 720 : ℝ)).fun_sub h2).fun_add h3).fun_sub h4).congr_deriv
      (by dsimp [p3R]; ring)
  have hp4L : ∀ r, HasDerivAt p4L (p3L r) r := by
    intro r
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 24) (r / 12) r :=
      ((hasDerivAt_pow 2 r).div_const 24).congr_deriv (by ring)
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 12) (r ^ 2 / 4) r :=
      ((hasDerivAt_pow 3 r).div_const 12).congr_deriv (by ring)
    have h4 : HasDerivAt (fun x : ℝ => x ^ 4 / 24) (r ^ 3 / 6) r :=
      ((hasDerivAt_pow 4 r).div_const 24).congr_deriv (by ring)
    exact ((((hasDerivAt_const r (1 / 720 : ℝ)).fun_sub h2).fun_sub h3).fun_sub h4).congr_deriv
      (by dsimp [p3L]; ring)
  have hp5R : ∀ r, HasDerivAt p5R (p4R r) r := by
    intro r
    have h1 : HasDerivAt (fun x : ℝ => x / 720) (1 / 720) r := by
      simpa using (hasDerivAt_id r).div_const 720
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 72) (r ^ 2 / 24) r :=
      ((hasDerivAt_pow 3 r).div_const 72).congr_deriv (by ring)
    have h4 : HasDerivAt (fun x : ℝ => x ^ 4 / 48) (r ^ 3 / 12) r :=
      ((hasDerivAt_pow 4 r).div_const 48).congr_deriv (by ring)
    have h5d : HasDerivAt (fun x : ℝ => x ^ 5 / 120) (r ^ 4 / 24) r :=
      ((hasDerivAt_pow 5 r).div_const 120).congr_deriv (by ring)
    exact (((h1.fun_sub h3).fun_add h4).fun_sub h5d).congr_deriv (by dsimp [p4R])
  have hp5L : ∀ r, HasDerivAt p5L (p4L r) r := by
    intro r
    have h1 : HasDerivAt (fun x : ℝ => x / 720) (1 / 720) r := by
      simpa using (hasDerivAt_id r).div_const 720
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 72) (r ^ 2 / 24) r :=
      ((hasDerivAt_pow 3 r).div_const 72).congr_deriv (by ring)
    have h4 : HasDerivAt (fun x : ℝ => x ^ 4 / 48) (r ^ 3 / 12) r :=
      ((hasDerivAt_pow 4 r).div_const 48).congr_deriv (by ring)
    have h5d : HasDerivAt (fun x : ℝ => x ^ 5 / 120) (r ^ 4 / 24) r :=
      ((hasDerivAt_pow 5 r).div_const 120).congr_deriv (by ring)
    exact (((h1.fun_sub h3).fun_sub h4).fun_sub h5d).congr_deriv (by dsimp [p4L])
  have hshift3 : ∀ r, HasDerivAt (fun x => h''' (a + x)) (h4 (a + r)) r := by
    intro r
    have hcomp := (hh''' (a + r)).comp r ((hasDerivAt_id r).const_add a)
    exact hcomp.congr_deriv (by simp)
  have hshift4 : ∀ r, HasDerivAt (fun x => h4 (a + x)) (h5 (a + r)) r := by
    intro r
    have hcomp := (hh4 (a + r)).comp r ((hasDerivAt_id r).const_add a)
    exact hcomp.congr_deriv (by simp)
  have hR_eq3 : ∫ r in (0 : ℝ)..(1 / 2), P3 r * h''' (a + r) =
      ∫ r in (0 : ℝ)..(1 / 2), p3R r * h''' (a + r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hr
    simp [P3, p3R, hr.1]
  have hL_eq3 : ∫ r in (-1 / 2 : ℝ)..0, P3 r * h''' (a + r) =
      ∫ r in (-1 / 2 : ℝ)..0, p3L r * h''' (a + r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hr
    by_cases hr0 : r = 0
    · subst hr0; simp [P3, p3L]
    · have hlt : ¬(0 ≤ r) := fun h => hr0 (le_antisymm hr.2 h)
      simp [P3, p3L, hlt]
  have hR_eq5 : ∫ r in (0 : ℝ)..(1 / 2), P5 r * h5 (a + r) =
      ∫ r in (0 : ℝ)..(1 / 2), p5R r * h5 (a + r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hr
    simp [P5, p5R, hr.1]
  have hL_eq5 : ∫ r in (-1 / 2 : ℝ)..0, P5 r * h5 (a + r) =
      ∫ r in (-1 / 2 : ℝ)..0, p5L r * h5 (a + r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hr
    by_cases hr0 : r = 0
    · subst hr0; simp [P5, p5L]
    · have hlt : ¬(0 ≤ r) := fun h => hr0 (le_antisymm hr.2 h)
      simp [P5, p5L, hlt]
  have hR4 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun r => h''' (a + r))
    (u' := fun r => h4 (a + r)) (v := p4R) (v' := p3R) (a := (0 : ℝ)) (b := (1 / 2))
    (fun r _ => hshift3 r) (fun r _ => hp4R r)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by dsimp [p3R]; fun_prop) _ _)
  have hR5 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun r => h4 (a + r))
    (u' := fun r => h5 (a + r)) (v := p5R) (v' := p4R) (a := (0 : ℝ)) (b := (1 / 2))
    (fun r _ => hshift4 r) (fun r _ => hp5R r)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by dsimp [p4R]; fun_prop) _ _)
  have hL4 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun r => h''' (a + r))
    (u' := fun r => h4 (a + r)) (v := p4L) (v' := p3L) (a := (-1 / 2 : ℝ)) (b := 0)
    (fun r _ => hshift3 r) (fun r _ => hp4L r)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by dsimp [p3L]; fun_prop) _ _)
  have hL5 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun r => h4 (a + r))
    (u' := fun r => h5 (a + r)) (v := p5L) (v' := p4L) (a := (-1 / 2 : ℝ)) (b := 0)
    (fun r _ => hshift4 r) (fun r _ => hp5L r)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by dsimp [p4L]; fun_prop) _ _)
  have hv4R : p4R (1 / 2) = -7 / 5760 ∧ p4R 0 = 1 / 720 ∧ p5R (1 / 2) = 0 ∧ p5R 0 = 0 := by
    dsimp [p4R, p5R]; norm_num
  have hv4L : p4L 0 = 1 / 720 ∧ p4L (-1 / 2) = -7 / 5760 ∧ p5L 0 = 0 ∧ p5L (-1 / 2) = 0 := by
    dsimp [p4L, p5L]; norm_num
  have ha0 : a + 0 = a := add_zero a
  have ha_sub : a + (-1 / 2 : ℝ) = a - 1 / 2 := by ring
  have hcR3 : ∫ r in (0 : ℝ)..(1 / 2), p3R r * h''' (a + r) = ∫ x in (0 : ℝ)..(1 / 2), h''' (a + x) * p3R x :=
    intervalIntegral.integral_congr fun _ _ => mul_comm _ _
  have hcL3 : ∫ r in (-1 / 2 : ℝ)..0, p3L r * h''' (a + r) = ∫ x in (-1 / 2 : ℝ)..0, h''' (a + x) * p3L x :=
    intervalIntegral.integral_congr fun _ _ => mul_comm _ _
  have hcR4 : ∫ x in (0 : ℝ)..(1 / 2), h4 (a + x) * p4R x = ∫ x in (0 : ℝ)..(1 / 2), p4R x * h4 (a + x) :=
    intervalIntegral.integral_congr fun _ _ => mul_comm _ _
  have hcL4 : ∫ x in (-1 / 2 : ℝ)..0, h4 (a + x) * p4L x = ∫ x in (-1 / 2 : ℝ)..0, p4L x * h4 (a + x) :=
    intervalIntegral.integral_congr fun _ _ => mul_comm _ _
  have hcR5 : ∫ x in (0 : ℝ)..(1 / 2), h5 (a + x) * p5R x = ∫ r in (0 : ℝ)..(1 / 2), p5R r * h5 (a + r) :=
    intervalIntegral.integral_congr fun _ _ => mul_comm _ _
  have hcL5 : ∫ x in (-1 / 2 : ℝ)..0, h5 (a + x) * p5L x = ∫ r in (-1 / 2 : ℝ)..0, p5L r * h5 (a + r) :=
    intervalIntegral.integral_congr fun _ _ => mul_comm _ _
  rw [hR_eq3, hL_eq3, hcR3, hcL3, hR4, hL4] at hp3
  rw [hR5, hL5, hcR5, hcL5] at hp3
  rw [hR_eq5, hL_eq5]
  rcases hv4R with ⟨hr4_1, hr4_0, hr5_1, hr5_0⟩
  rcases hv4L with ⟨hl4_0, hl4_1, hl5_0, hl5_1⟩
  rw [hr4_1, hr4_0, hr5_1, hr5_0, hl4_0, hl4_1, hl5_0, hl5_1, ha0, ha_sub] at hp3
  linarith

private lemma phi5_nonneg_integral_le (M : ℝ) (_hM : 0 ≤ M) :
    ∫ z in (0 : ℝ)..M, |(64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120) * Real.exp (-z ^ 2)| ≤ 100 := by
  let G : ℝ → ℝ := fun z => |(64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120) * Real.exp (-z ^ 2)|
  let phi4 : ℝ → ℝ := fun z => (-32 * z ^ 5 + 160 * z ^ 3 - 120 * z) * Real.exp (-z ^ 2)
  let phi5 : ℝ → ℝ := fun z => (64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120) * Real.exp (-z ^ 2)
  have hG_cont : Continuous G := by fun_prop
  have hphi4_deriv : ∀ z : ℝ, HasDerivAt phi4 (phi5 z) z := by
    intro z
    have hpoly : HasDerivAt (fun x : ℝ => -32 * x ^ 5 + 160 * x ^ 3 - 120 * x)
        (-160 * z ^ 4 + 480 * z ^ 2 - 120) z := by
      have h1 : HasDerivAt (fun x : ℝ => -32 * x ^ 5) (-160 * z ^ 4) z :=
        ((hasDerivAt_pow 5 z).const_mul (-32 : ℝ)).congr_deriv (by ring)
      have h2 : HasDerivAt (fun x : ℝ => 160 * x ^ 3) (480 * z ^ 2) z :=
        ((hasDerivAt_pow 3 z).const_mul (160 : ℝ)).congr_deriv (by ring)
      have h3 : HasDerivAt (fun x : ℝ => 120 * x) 120 z := by
        simpa using (hasDerivAt_id z).const_mul (120 : ℝ)
      exact ((h1.fun_add h2).fun_sub h3).congr_deriv (by ring)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2)) (-2 * z * Real.exp (-z ^ 2)) z := by
      have hsq : HasDerivAt (fun x : ℝ => -x ^ 2) (-2 * z) z :=
        ((hasDerivAt_pow 2 z).fun_neg).congr_deriv (by ring)
      convert hsq.exp using 1; ring
    exact (hpoly.fun_mul hexp).congr_deriv (by dsimp [phi5]; ring)
  set M' := max M (12 / 5)
  have hMM' : M ≤ M' := le_max_left _ _
  have hM'_ge : 12 / 5 ≤ M' := le_max_right _ _
  have hsplit0 : ∫ z in (0 : ℝ)..M', G z = (∫ z in (0 : ℝ)..M, G z) + ∫ z in M..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hnonneg_tail : 0 ≤ ∫ z in M..M', G z :=
    intervalIntegral.integral_nonneg hMM' fun z _ => abs_nonneg _
  have hle_M' : ∫ z in (0 : ℝ)..M, G z ≤ ∫ z in (0 : ℝ)..M', G z := by
    linarith only [hsplit0, hnonneg_tail]
  -- Split [0, M'] at 21/50 (0.42), 9/20 (0.45), 13/10 (1.3), 137/100 (1.37), 58/25 (2.32), 119/50 (2.38)
  have hs1 : ∫ z in (0 : ℝ)..M', G z = (∫ z in (0 : ℝ)..(21 / 50), G z) + ∫ z in (21 / 50 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hs2 : ∫ z in (21 / 50 : ℝ)..M', G z = (∫ z in (21 / 50 : ℝ)..(9 / 20), G z) + ∫ z in (9 / 20 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hs3 : ∫ z in (9 / 20 : ℝ)..M', G z = (∫ z in (9 / 20 : ℝ)..(13 / 10), G z) + ∫ z in (13 / 10 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hs4 : ∫ z in (13 / 10 : ℝ)..M', G z = (∫ z in (13 / 10 : ℝ)..(137 / 100), G z) + ∫ z in (137 / 100 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hs5 : ∫ z in (137 / 100 : ℝ)..M', G z = (∫ z in (137 / 100 : ℝ)..(58 / 25), G z) + ∫ z in (58 / 25 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hs6 : ∫ z in (58 / 25 : ℝ)..M', G z = (∫ z in (58 / 25 : ℝ)..(119 / 50), G z) + ∫ z in (119 / 50 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hs7 : ∫ z in (119 / 50 : ℝ)..M', G z = (∫ z in (119 / 50 : ℝ)..(12 / 5), G z) + ∫ z in (12 / 5 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  -- Rational exponential bounds
  have he_042 : Real.exp (-(441 / 2500 : ℝ)) ≤ 8384 / 10000 := by
    have hp := exp_ge_poly3 (by norm_num : (0 : ℝ) ≤ 441 / 2500)
    rw [Real.exp_neg]
    exact le_trans ((inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hp) (by norm_num)
  have he_045 : Real.exp (-(81 / 400 : ℝ)) ≤ 8168 / 10000 := by
    have hp := exp_ge_poly3 (by norm_num : (0 : ℝ) ≤ 81 / 400)
    rw [Real.exp_neg]
    exact le_trans ((inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hp) (by norm_num)
  have he_130 : Real.exp (-(169 / 100 : ℝ)) ≤ 18598 / 100000 := by
    have hp := exp_ge_poly5 (by norm_num : (0 : ℝ) ≤ 169 / 100)
    rw [Real.exp_neg]
    exact le_trans ((inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hp) (by norm_num)
  have he_137 : Real.exp (-(18769 / 10000 : ℝ)) ≤ 15505 / 100000 := by
    have hp := exp_ge_poly5 (by norm_num : (0 : ℝ) ≤ 18769 / 10000)
    rw [Real.exp_neg]
    exact le_trans ((inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hp) (by norm_num)
  have he_232 : Real.exp (-(3364 / 625 : ℝ)) ≤ 4829 / 1000000 := by
    have hp := exp_ge_poly9 (by norm_num : (0 : ℝ) ≤ 3364 / 625)
    rw [Real.exp_neg]
    exact le_trans ((inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hp) (by norm_num)
  have he_240 : Real.exp (-(144 / 25 : ℝ)) ≤ 339 / 100000 := by
    have hp := exp_ge_poly9 (by norm_num : (0 : ℝ) ≤ 144 / 25)
    rw [Real.exp_neg]
    exact le_trans ((inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hp) (by norm_num)
  -- Piece 1: [0, 21/50]
  have hb1 : ∫ z in (0 : ℝ)..(21 / 50), G z ≤ 3267 / 100 := by
    have heq : ∫ z in (0 : ℝ)..(21 / 50), G z = ∫ z in (0 : ℝ)..(21 / 50), -phi5 z := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hz
      have hu : z ^ 2 ≤ 441 / 2500 := by nlinarith only [hz.1, hz.2]
      have hu3 : 0 ≤ (z ^ 2) ^ 3 := by positivity
      have hsq : 8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15 =
          -60 * (z ^ 2 - 3 / 4) ^ 2 + 75 / 4 + 8 * (z ^ 2) ^ 3 := by ring
      have hbd : z ^ 2 - 3 / 4 ≤ -(1434 / 2500 : ℝ) := by linarith only [hu]
      have hsq_lo : (1434 / 2500 : ℝ) ^ 2 ≤ (z ^ 2 - 3 / 4) ^ 2 := by nlinarith only [hbd]
      have hu3_ub : (z ^ 2) ^ 3 ≤ (441 / 2500 : ℝ) ^ 3 :=
        pow_le_pow_left₀ (sq_nonneg z) hu 3
      have hpoly : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 ≤ 0 := by
        have h8 : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 =
            8 * (8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15) := by ring
        linarith only [h8, hsq, hsq_lo, hu3_ub]
      have hle0 : phi5 z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpoly (Real.exp_pos _).le
      exact abs_of_nonpos hle0
    rw [heq, intervalIntegral.integral_neg]
    have hftc : ∫ z in (0 : ℝ)..(21 / 50), phi5 z = phi4 (21 / 50) - phi4 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hphi4_deriv z)
        (Continuous.intervalIntegrable (by dsimp [phi5]; fun_prop) (0 : ℝ) (21 / 50))
    rw [hftc]
    have h0 : phi4 0 = 0 := by dsimp [phi4]; norm_num
    have hv : -phi4 (21 / 50) = (120 * (21 / 50 : ℝ) - 160 * (21 / 50) ^ 3 + 32 * (21 / 50) ^ 5) *
        Real.exp (-(441 / 2500 : ℝ)) := by
      dsimp [phi4]; ring_nf
    rw [h0, sub_zero, hv]
    nlinarith only [he_042]
  -- Piece 2: [21/50, 9/20]
  have hb2 : ∫ z in (21 / 50 : ℝ)..(9 / 20), G z ≤ 49 / 100 := by
    have hC2 : (96 / 5 : ℝ) * (8384 / 10000) ≤ 161 / 10 := by norm_num
    have hpt : ∀ z ∈ Set.Icc (21 / 50 : ℝ) (9 / 20), G z ≤ (161 / 10 : ℝ) := by
      intro z hz
      have hu_lo : 441 / 2500 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hu_hi : z ^ 2 ≤ 81 / 400 := by nlinarith only [hz.1, hz.2]
      have hfac : 8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15 =
          8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2) + (-88 / 100 * z ^ 2 + 84 / 100) := by ring
      have h1 : |z ^ 2 - 1 / 5| ≤ 24 / 1000 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have h2 : |z ^ 2 - 9 / 5| ≤ 163 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have h3 : |z ^ 2 - 11 / 2| ≤ 533 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have hprod : |8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2)| ≤ 8 * (24 / 1000) * (163 / 100) * (533 / 100) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num)]
        have h12 : |z ^ 2 - 1 / 5| * |z ^ 2 - 9 / 5| ≤ (24 / 1000) * (163 / 100) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        have h123 : (|z ^ 2 - 1 / 5| * |z ^ 2 - 9 / 5|) * |z ^ 2 - 11 / 2| ≤
            ((24 / 1000) * (163 / 100)) * (533 / 100) :=
          mul_le_mul h12 h3 (abs_nonneg _) (by norm_num)
        linarith only [h123]
      have hlin : |-88 / 100 * z ^ 2 + 84 / 100| ≤ 69 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_hi], by linarith only [hu_lo]⟩
      have hp_abs : |8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15| ≤ 24 / 10 := by
        have htri : |8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15| ≤
            |8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2)| + |-88 / 100 * z ^ 2 + 84 / 100| := by
          rw [hfac]
          exact abs_add_le _ _
        linarith only [htri, hprod, hlin]
      have h64 : |64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120| ≤ 96 / 5 := by
        have hid : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 =
            8 * (8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15) := by ring
        rw [hid, abs_mul, abs_of_nonneg (by norm_num)]
        linarith only [hp_abs]
      have hexp : Real.exp (-z ^ 2) ≤ 8384 / 10000 :=
        le_trans (Real.exp_le_exp.mpr (by linarith only [hu_lo])) he_042
      dsimp [G]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact le_trans (mul_le_mul h64 hexp (Real.exp_pos _).le (by norm_num)) hC2
    have hi := intervalIntegral.integral_mono_on (by norm_num)
      (hG_cont.intervalIntegrable (21 / 50 : ℝ) (9 / 20))
      (intervalIntegrable_const (μ := volume) (a := (21 / 50 : ℝ)) (b := (9 / 20 : ℝ)) (c := (161 / 10 : ℝ))) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    linarith only [hi]
  -- Piece 3: [9/20, 13/10]
  have hb3 : ∫ z in (9 / 20 : ℝ)..(13 / 10), G z ≤ 4695 / 100 := by
    have heq : ∫ z in (9 / 20 : ℝ)..(13 / 10), G z = ∫ z in (9 / 20 : ℝ)..(13 / 10), phi5 z := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hz
      have hu_lo : 81 / 400 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hu_hi : z ^ 2 ≤ 169 / 100 := by nlinarith only [hz.1, hz.2]
      have hfac : 8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15 =
          8 * (z ^ 2 - 1 / 5) * (7 / 4 - z ^ 2) * (11 / 2 - z ^ 2) +
            (-4 / 10 * (z ^ 2) ^ 2 + 14 / 10 * z ^ 2 + 4 / 10) := by ring
      have h1 : 0 ≤ 8 * (z ^ 2 - 1 / 5) * (7 / 4 - z ^ 2) * (11 / 2 - z ^ 2) := by
        have a1 : 0 ≤ z ^ 2 - 1 / 5 := by linarith
        have a2 : 0 ≤ 7 / 4 - z ^ 2 := by linarith
        have a3 : 0 ≤ 11 / 2 - z ^ 2 := by linarith
        positivity
      have h2 : 0 ≤ -4 / 10 * (z ^ 2) ^ 2 + 14 / 10 * z ^ 2 + 4 / 10 := by
        have hq : -4 / 10 * (z ^ 2) ^ 2 + 14 / 10 * z ^ 2 + 4 / 10 =
            -4 / 10 * (z ^ 2 - 7 / 4) ^ 2 + 13 / 8 := by ring
        have hbd : (z ^ 2 - 7 / 4) ^ 2 ≤ (619 / 400 : ℝ) ^ 2 := by nlinarith only [hu_lo, hu_hi]
        linarith only [hq, hbd]
      have hpoly : 0 ≤ 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 := by
        have h8 : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 =
            8 * (8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15) := by ring
        linarith
      exact abs_of_nonneg (mul_nonneg hpoly (Real.exp_pos _).le)
    rw [heq]
    have hftc : ∫ z in (9 / 20 : ℝ)..(13 / 10), phi5 z = phi4 (13 / 10) - phi4 (9 / 20) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hphi4_deriv z)
        (Continuous.intervalIntegrable (by dsimp [phi5]; fun_prop) (9 / 20 : ℝ) (13 / 10))
    rw [hftc]
    have hv1 : phi4 (13 / 10) = (-32 * (13 / 10 : ℝ) ^ 5 + 160 * (13 / 10) ^ 3 - 120 * (13 / 10)) *
        Real.exp (-(169 / 100 : ℝ)) := by dsimp [phi4]; ring_nf
    have hv2 : -phi4 (9 / 20) = (120 * (9 / 20 : ℝ) - 160 * (9 / 20) ^ 3 + 32 * (9 / 20) ^ 5) *
        Real.exp (-(81 / 400 : ℝ)) := by dsimp [phi4]; ring_nf
    have hsub : phi4 (13 / 10) - phi4 (9 / 20) = phi4 (13 / 10) + (-phi4 (9 / 20)) := sub_eq_add_neg _ _
    rw [hsub, hv1, hv2]
    nlinarith only [he_130, he_045]
  -- Piece 4: [13/10, 137/100]
  have hb4 : ∫ z in (13 / 10 : ℝ)..(137 / 100), G z ≤ 95 / 100 := by
    have hC4 : (72 : ℝ) * (18598 / 100000) ≤ 135 / 10 := by norm_num
    have hpt : ∀ z ∈ Set.Icc (13 / 10 : ℝ) (137 / 100), G z ≤ (135 / 10 : ℝ) := by
      intro z hz
      have hu_lo : 169 / 100 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hu_hi : z ^ 2 ≤ 18769 / 10000 := by nlinarith only [hz.1, hz.2]
      have hfac : 8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15 =
          8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2) + (-88 / 100 * z ^ 2 + 84 / 100) := by ring
      have h1 : |z ^ 2 - 1 / 5| ≤ 168 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have h2 : |z ^ 2 - 9 / 5| ≤ 11 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have h3 : |z ^ 2 - 11 / 2| ≤ 381 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have hprod : |8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2)| ≤
          8 * (168 / 100) * (11 / 100) * (381 / 100) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num)]
        have h12 : |z ^ 2 - 1 / 5| * |z ^ 2 - 9 / 5| ≤ (168 / 100) * (11 / 100) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        have h123 : (|z ^ 2 - 1 / 5| * |z ^ 2 - 9 / 5|) * |z ^ 2 - 11 / 2| ≤
            ((168 / 100) * (11 / 100)) * (381 / 100) :=
          mul_le_mul h12 h3 (abs_nonneg _) (by norm_num)
        linarith only [h123]
      have hlin : |-88 / 100 * z ^ 2 + 84 / 100| ≤ 250 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_hi], by linarith only [hu_lo]⟩
      have hp_abs : |8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15| ≤ 9 := by
        have htri : |8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15| ≤
            |8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2)| + |-88 / 100 * z ^ 2 + 84 / 100| := by
          rw [hfac]
          exact abs_add_le _ _
        linarith only [htri, hprod, hlin]
      have h64 : |64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120| ≤ 72 := by
        have hid : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 =
            8 * (8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15) := by ring
        rw [hid, abs_mul, abs_of_nonneg (by norm_num)]
        linarith only [hp_abs]
      have hexp : Real.exp (-z ^ 2) ≤ 18598 / 100000 :=
        le_trans (Real.exp_le_exp.mpr (by linarith only [hu_lo])) he_130
      dsimp [G]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact le_trans (mul_le_mul h64 hexp (Real.exp_pos _).le (by norm_num)) hC4
    have hi := intervalIntegral.integral_mono_on (by norm_num)
      (hG_cont.intervalIntegrable (13 / 10 : ℝ) (137 / 100))
      (intervalIntegrable_const (μ := volume) (a := (13 / 10 : ℝ)) (b := (137 / 100 : ℝ)) (c := (135 / 10 : ℝ))) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    linarith only [hi]
  -- Piece 5: [137/100, 58/25]
  have hb5 : ∫ z in (137 / 100 : ℝ)..(58 / 25), G z ≤ 1644 / 100 := by
    have heq : ∫ z in (137 / 100 : ℝ)..(58 / 25), G z = ∫ z in (137 / 100 : ℝ)..(58 / 25), -phi5 z := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hz
      have hu_lo : 18769 / 10000 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hu_hi : z ^ 2 ≤ 3364 / 625 := by nlinarith only [hz.1, hz.2]
      have hfac : 8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15 =
          8 * (z ^ 2 - 15 / 100) * (185 / 100 - z ^ 2) * (545 / 100 - z ^ 2) +
            (-4 / 10 * (z ^ 2) ^ 2 + 58 / 100 * z ^ 2 - 2901 / 1000) := by ring
      have h1 : 8 * (z ^ 2 - 15 / 100) * (185 / 100 - z ^ 2) * (545 / 100 - z ^ 2) ≤ 0 := by
        have a1 : 0 ≤ z ^ 2 - 15 / 100 := by linarith only [hu_lo]
        have a2 : 0 ≤ z ^ 2 - 185 / 100 := by linarith only [hu_lo]
        have a3 : 0 ≤ 545 / 100 - z ^ 2 := by linarith only [hu_hi]
        have hpos_p : 0 ≤ 8 * (z ^ 2 - 15 / 100) * (z ^ 2 - 185 / 100) * (545 / 100 - z ^ 2) := by
          positivity
        linarith only [hpos_p]
      have h2 : -4 / 10 * (z ^ 2) ^ 2 + 58 / 100 * z ^ 2 - 2901 / 1000 ≤ 0 := by
        have hq : -4 / 10 * (z ^ 2) ^ 2 + 58 / 100 * z ^ 2 - 2901 / 1000 =
            -4 / 10 * (z ^ 2 - 29 / 40) ^ 2 - 269075 / 100000 := by ring
        have hsq_nn : 0 ≤ (z ^ 2 - 29 / 40) ^ 2 := sq_nonneg _
        linarith only [hq, hsq_nn]
      have hpoly : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 ≤ 0 := by
        have h8 : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 =
            8 * (8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15) := by ring
        linarith only [h8, hfac, h1, h2]
      exact abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hpoly (Real.exp_pos _).le)
    rw [heq, intervalIntegral.integral_neg]
    have hftc : ∫ z in (137 / 100 : ℝ)..(58 / 25), phi5 z = phi4 (58 / 25) - phi4 (137 / 100) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hphi4_deriv z)
        (Continuous.intervalIntegrable (by dsimp [phi5]; fun_prop) (137 / 100 : ℝ) (58 / 25))
    rw [hftc]
    have hv1 : phi4 (137 / 100) = (-32 * (137 / 100 : ℝ) ^ 5 + 160 * (137 / 100) ^ 3 - 120 * (137 / 100)) *
        Real.exp (-(18769 / 10000 : ℝ)) := by dsimp [phi4]; ring_nf
    have hv2 : -phi4 (58 / 25) = (32 * (58 / 25 : ℝ) ^ 5 - 160 * (58 / 25) ^ 3 + 120 * (58 / 25)) *
        Real.exp (-(3364 / 625 : ℝ)) := by dsimp [phi4]; ring_nf
    have hsub : -(phi4 (58 / 25) - phi4 (137 / 100)) = phi4 (137 / 100) + (-phi4 (58 / 25)) := by ring
    rw [hsub, hv1, hv2]
    nlinarith only [he_137, he_232]
  -- Piece 6: [58/25, 119/50] and [119/50, 12/5] combined on [58/25, 12/5] (width 2/25 = 0.08)!
  have hb67 : ∫ z in (58 / 25 : ℝ)..(12 / 5), G z ≤ 16 / 100 := by
    have hC67 : (408 : ℝ) * (4829 / 1000000) ≤ 198 / 100 := by norm_num
    have hpt : ∀ z ∈ Set.Icc (58 / 25 : ℝ) (12 / 5), G z ≤ (198 / 100 : ℝ) := by
      intro z hz
      have hu_lo : 3364 / 625 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hu_hi : z ^ 2 ≤ 144 / 25 := by nlinarith only [hz.1, hz.2]
      have hfac : 8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15 =
          8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2) + (-88 / 100 * z ^ 2 + 84 / 100) := by ring
      have h1 : |z ^ 2 - 1 / 5| ≤ 556 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have h2 : |z ^ 2 - 9 / 5| ≤ 396 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have h3 : |z ^ 2 - 11 / 2| ≤ 26 / 100 :=
        abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
      have hprod : |8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2)| ≤
          8 * (556 / 100) * (396 / 100) * (26 / 100) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num)]
        have h12 : |z ^ 2 - 1 / 5| * |z ^ 2 - 9 / 5| ≤ (556 / 100) * (396 / 100) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        have h123 : (|z ^ 2 - 1 / 5| * |z ^ 2 - 9 / 5|) * |z ^ 2 - 11 / 2| ≤
            ((556 / 100) * (396 / 100)) * (26 / 100) :=
          mul_le_mul h12 h3 (abs_nonneg _) (by norm_num)
        linarith only [h123]
      have hlin : |-88 / 100 * z ^ 2 + 84 / 100| ≤ 5 :=
        abs_le.mpr ⟨by linarith only [hu_hi], by linarith only [hu_lo]⟩
      have hp_abs : |8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15| ≤ 51 := by
        have htri : |8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15| ≤
            |8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 11 / 2)| + |-88 / 100 * z ^ 2 + 84 / 100| := by
          rw [hfac]
          exact abs_add_le _ _
        linarith only [htri, hprod, hlin]
      have h64 : |64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120| ≤ 408 := by
        have hid : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 =
            8 * (8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15) := by ring
        rw [hid, abs_mul, abs_of_nonneg (by norm_num)]
        linarith only [hp_abs]
      have hexp : Real.exp (-z ^ 2) ≤ 4829 / 1000000 :=
        le_trans (Real.exp_le_exp.mpr (by linarith only [hu_lo])) he_232
      dsimp [G]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact le_trans (mul_le_mul h64 hexp (Real.exp_pos _).le (by norm_num)) hC67
    have hi := intervalIntegral.integral_mono_on (by norm_num)
      (hG_cont.intervalIntegrable (58 / 25 : ℝ) (12 / 5))
      (intervalIntegrable_const (μ := volume) (a := (58 / 25 : ℝ)) (b := (12 / 5 : ℝ)) (c := (198 / 100 : ℝ))) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    linarith only [hi]
  -- Piece 8: [12/5, M']
  have hb8 : ∫ z in (12 / 5 : ℝ)..M', G z ≤ 212 / 100 := by
    have heq : ∫ z in (12 / 5 : ℝ)..M', G z = ∫ z in (12 / 5 : ℝ)..M', phi5 z := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [Set.uIcc_of_le hM'_ge] at hz
      have hu_lo : 144 / 25 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hfac : 8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15 =
          8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 28 / 5) +
            (4 / 5 * (z ^ 2 - 155 / 100) ^ 2 - 794 / 1000) := by ring
      have h1 : 0 ≤ 8 * (z ^ 2 - 1 / 5) * (z ^ 2 - 9 / 5) * (z ^ 2 - 28 / 5) := by
        have a1 : 0 ≤ z ^ 2 - 1 / 5 := by linarith only [hu_lo]
        have a2 : 0 ≤ z ^ 2 - 9 / 5 := by linarith only [hu_lo]
        have a3 : 0 ≤ z ^ 2 - 28 / 5 := by linarith only [hu_lo]
        positivity
      have h2 : 0 ≤ 4 / 5 * (z ^ 2 - 155 / 100) ^ 2 - 794 / 1000 := by
        have hbd : (144 / 25 - 155 / 100 : ℝ) ^ 2 ≤ (z ^ 2 - 155 / 100) ^ 2 := by nlinarith only [hu_lo]
        linarith only [hbd]
      have hpoly : 0 ≤ 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 := by
        have h8 : 64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120 =
            8 * (8 * (z ^ 2) ^ 3 - 60 * (z ^ 2) ^ 2 + 90 * z ^ 2 - 15) := by ring
        linarith only [h8, hfac, h1, h2]
      exact abs_of_nonneg (mul_nonneg hpoly (Real.exp_pos _).le)
    rw [heq]
    have hftc : ∫ z in (12 / 5 : ℝ)..M', phi5 z = phi4 M' - phi4 (12 / 5) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hphi4_deriv z)
        (Continuous.intervalIntegrable (by dsimp [phi5]; fun_prop) (12 / 5 : ℝ) M')
    rw [hftc]
    have hphi4_nonpos : phi4 M' ≤ 0 := by
      dsimp [phi4]
      have hpoly : -32 * M' ^ 5 + 160 * M' ^ 3 - 120 * M' ≤ 0 := by
        have hm2 : 144 / 25 ≤ M' ^ 2 := by nlinarith only [hM'_ge]
        have h1 : 0 ≤ 4 * (M' ^ 2 - 5 / 2) ^ 2 - 10 := by
          have hbd : (144 / 25 - 5 / 2 : ℝ) ^ 2 ≤ (M' ^ 2 - 5 / 2) ^ 2 := by nlinarith only [hm2]
          linarith only [hbd]
        have hfac : -32 * M' ^ 5 + 160 * M' ^ 3 - 120 * M' =
            -8 * M' * (4 * (M' ^ 2 - 5 / 2) ^ 2 - 10) := by ring
        have hm0 : 0 ≤ M' := by linarith only [hM'_ge]
        nlinarith only [hfac, h1, hm0]
      exact mul_nonpos_of_nonpos_of_nonneg hpoly (Real.exp_pos _).le
    have hv : -phi4 (12 / 5) = (32 * (12 / 5 : ℝ) ^ 5 - 160 * (12 / 5) ^ 3 + 120 * (12 / 5)) *
        Real.exp (-(144 / 25 : ℝ)) := by dsimp [phi4]; ring_nf
    nlinarith only [hphi4_nonpos, hv, he_240]
  have hs67 : ∫ z in (58 / 25 : ℝ)..M', G z = (∫ z in (58 / 25 : ℝ)..(12 / 5), G z) + ∫ z in (12 / 5 : ℝ)..M', G z :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  linarith only [hle_M', hs1, hs2, hs3, hs4, hs5, hs67, hb1, hb2, hb3, hb4, hb5, hb67, hb8]

private lemma phi5_integral_bound (a b : ℝ) (_hab : a ≤ b) :
    ∫ z in a..b, |(64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120) * Real.exp (-z ^ 2)| ≤ 200 := by
  let G : ℝ → ℝ := fun z => |(64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120) * Real.exp (-z ^ 2)|
  have hG_cont : Continuous G := by fun_prop
  set M := max |a| |b|
  have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
  have haM : -M ≤ a := by linarith [neg_abs_le a, le_max_left |a| |b|]
  have hbM : b ≤ M := le_trans (le_abs_self b) (le_max_right _ _)
  have hsplit1 : ∫ z in (-M)..M, G z = (∫ z in (-M)..a, G z) + (∫ z in a..M, G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hsplit2 : ∫ z in a..M, G z = (∫ z in a..b, G z) + (∫ z in b..M, G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hnn1 : 0 ≤ ∫ z in (-M)..a, G z :=
    intervalIntegral.integral_nonneg haM fun z _ => abs_nonneg _
  have hnn2 : 0 ≤ ∫ z in b..M, G z :=
    intervalIntegral.integral_nonneg hbM fun z _ => abs_nonneg _
  have hsub : ∫ z in a..b, G z ≤ ∫ z in (-M)..M, G z := by linarith
  have heven : ∫ z in (-M)..0, G z = ∫ z in (0 : ℝ)..M, G z := by
    have hc := intervalIntegral.integral_comp_neg G (a := (0 : ℝ)) (b := M)
    have hG_even : ∀ z, G (-z) = G z := fun z => by dsimp [G]; ring_nf
    simp_rw [hG_even, neg_zero] at hc
    exact hc.symm
  have hsplit : ∫ z in (-M)..M, G z = (∫ z in (-M)..0, G z) + (∫ z in (0 : ℝ)..M, G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hhalf := phi5_nonneg_integral_le M hM0
  linarith

private lemma f_sixth_integral_bound (a b t : ℝ) (ht : 0 < t) (hab : a ≤ b) :
    ∫ u in a..b, |t ^ 3 * (64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120) * Real.exp (-u ^ 2 * t)| ≤
      200 * t ^ 2 * √t := by
  let G : ℝ → ℝ := fun z => |(64 * z ^ 6 - 480 * z ^ 4 + 720 * z ^ 2 - 120) * Real.exp (-z ^ 2)|
  have hsqrt : 0 < √t := Real.sqrt_pos.mpr ht
  have hsq : √t ^ 2 = t := Real.sq_sqrt ht.le
  have hcomp := intervalIntegral.integral_comp_mul_left G hsqrt.ne' (a := a) (b := b)
  have heq : ∫ u in a..b, |t ^ 3 * (64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120) * Real.exp (-u ^ 2 * t)| =
      t ^ 2 * √t * ∫ z in (√t * a)..(√t * b), G z := by
    have hpt : (fun u => |t ^ 3 * (64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120) * Real.exp (-u ^ 2 * t)|) =
        (fun u => t ^ 3 * G (√t * u)) := by
      ext u
      dsimp [G]
      have hid1 : 64 * (√t * u) ^ 6 - 480 * (√t * u) ^ 4 + 720 * (√t * u) ^ 2 - 120 =
          64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120 := by
        calc 64 * (√t * u) ^ 6 - 480 * (√t * u) ^ 4 + 720 * (√t * u) ^ 2 - 120
            = 64 * ((√t ^ 2) ^ 3 * u ^ 6) - 480 * ((√t ^ 2) ^ 2 * u ^ 4) + 720 * (√t ^ 2 * u ^ 2) - 120 := by ring
          _ = 64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120 := by rw [hsq]; ring
      have hid2 : -(√t * u) ^ 2 = -u ^ 2 * t := by
        calc -(√t * u) ^ 2 = -(√t ^ 2 * u ^ 2) := by ring
          _ = -u ^ 2 * t := by rw [hsq]; ring
      rw [hid1, hid2]
      calc |t ^ 3 * (64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120) * Real.exp (-u ^ 2 * t)|
          = |t ^ 3| * |(64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120) * Real.exp (-u ^ 2 * t)| := by
            rw [mul_assoc, abs_mul]
        _ = t ^ 3 * |(64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120) * Real.exp (-u ^ 2 * t)| := by
            rw [abs_of_nonneg (pow_nonneg ht.le 3)]
    rw [hpt, intervalIntegral.integral_const_mul, hcomp, smul_eq_mul]
    have htsq : t ^ 3 * (√t)⁻¹ = t ^ 2 * √t := by
      calc t ^ 3 * (√t)⁻¹ = t ^ 2 * √t ^ 2 * (√t)⁻¹ := by rw [hsq]; ring
        _ = t ^ 2 * √t := by field_simp
    rw [← mul_assoc, htsq]
  rw [heq]
  have hle := phi5_integral_bound (√t * a) (√t * b) (mul_le_mul_of_nonneg_left hab hsqrt.le)
  have hpos : 0 ≤ t ^ 2 * √t := by positivity
  nlinarith

private lemma P5_gauss_bounds (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) +
        2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * u * (2 * u ^ 2 * t - 3) * Real.exp (-u ^ 2 * t)
    let h''' : ℝ → ℝ := fun w => f3 (w - δ) - f3 (w + δ)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
    |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) - (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) -
      (1 / 24) * h' a₀ + (7 / 5760) * h''' a₀| ≤ (1 / 24) * (2 * δ) * t ^ 2 * √t := by
  intro h h' f3 h'''
  let f : ℝ → ℝ := fun u => Real.exp (-u ^ 2 * t)
  let f1 : ℝ → ℝ := fun u => -2 * t * u * Real.exp (-u ^ 2 * t)
  let f2 : ℝ → ℝ := fun u => 2 * t * (2 * u ^ 2 * t - 1) * Real.exp (-u ^ 2 * t)
  let f4 : ℝ → ℝ := fun u => 4 * t ^ 2 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)
  let f5 : ℝ → ℝ := fun u => 8 * t ^ 3 * u * (-4 * u ^ 4 * t ^ 2 + 20 * u ^ 2 * t - 15) * Real.exp (-u ^ 2 * t)
  let f6 : ℝ → ℝ := fun u => t ^ 3 * (64 * u ^ 6 * t ^ 3 - 480 * u ^ 4 * t ^ 2 + 720 * u ^ 2 * t - 120) * Real.exp (-u ^ 2 * t)
  have hf1 : ∀ u, HasDerivAt f (f1 u) u := by
    intro u
    have hsq : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * t * u) u :=
      (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
    exact (hsq.exp).congr_deriv (by dsimp [f1]; ring)
  have hf2 : ∀ u, HasDerivAt f1 (f2 u) u := by
    intro u
    have ha : HasDerivAt (fun x : ℝ => -2 * t * x) (-2 * t) u := by
      simpa using (hasDerivAt_id u).const_mul (-2 * t)
    exact (ha.fun_mul (hf1 u)).congr_deriv (by dsimp [f1, f2]; ring)
  have hf3 : ∀ u, HasDerivAt f2 (f3 u) u := by
    intro u
    have hpoly : HasDerivAt (fun x : ℝ => 2 * t * (2 * x ^ 2 * t - 1)) (8 * t ^ 2 * u) u := by
      have hp := ((hasDerivAt_pow 2 u).const_mul (2 : ℝ)).mul_const t
      exact ((hp.fun_sub (hasDerivAt_const u (1 : ℝ))).const_mul (2 * t)).congr_deriv (by ring)
    exact (hpoly.fun_mul (hf1 u)).congr_deriv (by dsimp [f1, f3]; ring)
  have hf4 : ∀ u, HasDerivAt f3 (f4 u) u := by
    intro u
    have hpoly : HasDerivAt (fun x : ℝ => -4 * t ^ 2 * x * (2 * x ^ 2 * t - 3))
        (-24 * t ^ 3 * u ^ 2 + 12 * t ^ 2) u := by
      have ha : HasDerivAt (fun x : ℝ => -4 * t ^ 2 * x) (-4 * t ^ 2) u :=
        ((hasDerivAt_id u).const_mul (-4 * t ^ 2)).congr_deriv (by ring)
      have hb : HasDerivAt (fun x : ℝ => 2 * x ^ 2 * t - 3) (4 * t * u) u := by
        have hp := ((hasDerivAt_pow 2 u).const_mul (2 : ℝ)).mul_const t
        exact (hp.fun_sub (hasDerivAt_const u (3 : ℝ))).congr_deriv (by ring)
      exact (ha.fun_mul hb).congr_deriv (by ring)
    exact (hpoly.fun_mul (hf1 u)).congr_deriv (by dsimp [f1, f4]; ring)
  have hf5 : ∀ u, HasDerivAt f4 (f5 u) u := by
    intro u
    have hpoly : HasDerivAt (fun x : ℝ => 4 * t ^ 2 * (4 * x ^ 4 * t ^ 2 - 12 * x ^ 2 * t + 3))
        (4 * t ^ 2 * (16 * u ^ 3 * t ^ 2 - 24 * u * t)) u := by
      have hp1 := ((hasDerivAt_pow 4 u).const_mul (4 : ℝ)).mul_const (t ^ 2)
      have hp2 := ((hasDerivAt_pow 2 u).const_mul (12 : ℝ)).mul_const t
      exact (((hp1.fun_sub hp2).fun_add (hasDerivAt_const u (3 : ℝ))).const_mul (4 * t ^ 2)).congr_deriv (by ring)
    exact (hpoly.fun_mul (hf1 u)).congr_deriv (by dsimp [f1, f5]; ring)
  have hf6 : ∀ u, HasDerivAt f5 (f6 u) u := by
    intro u
    have hpoly : HasDerivAt (fun x : ℝ => 8 * t ^ 3 * x * (-4 * x ^ 4 * t ^ 2 + 20 * x ^ 2 * t - 15))
        (8 * t ^ 3 * (-20 * u ^ 4 * t ^ 2 + 60 * u ^ 2 * t - 15)) u := by
      have ha : HasDerivAt (fun x : ℝ => 8 * t ^ 3 * x) (8 * t ^ 3) u :=
        ((hasDerivAt_id u).const_mul (8 * t ^ 3)).congr_deriv (by ring)
      have hp1 := ((hasDerivAt_pow 4 u).const_mul (-4 : ℝ)).mul_const (t ^ 2)
      have hp2 := ((hasDerivAt_pow 2 u).const_mul (20 : ℝ)).mul_const t
      have hb : HasDerivAt (fun x : ℝ => -4 * x ^ 4 * t ^ 2 + 20 * x ^ 2 * t - 15)
          (-16 * u ^ 3 * t ^ 2 + 40 * u * t) u :=
        ((hp1.fun_add hp2).fun_sub (hasDerivAt_const u (15 : ℝ))).congr_deriv (by ring)
      exact (ha.fun_mul hb).congr_deriv (by ring)
    exact (hpoly.fun_mul (hf1 u)).congr_deriv (by dsimp [f1, f6]; ring)
  let h'' : ℝ → ℝ := fun w => f2 (w - δ) - f2 (w + δ)
  let h4 : ℝ → ℝ := fun w => f4 (w - δ) - f4 (w + δ)
  let h5 : ℝ → ℝ := fun w => f5 (w - δ) - f5 (w + δ)
  have hh_deriv : ∀ w, HasDerivAt h (h' w) w := by
    intro w
    have h1 : HasDerivAt (fun x => f (x - δ)) (f1 (w - δ)) w := by
      have hc : HasDerivAt (f ∘ fun x => id x - δ) (f1 (w - δ) * 1) w :=
        (hf1 (w - δ)).comp w ((hasDerivAt_id w).sub_const δ)
      exact hc.congr_deriv (mul_one _)
    have h2 : HasDerivAt (fun x => f (x + δ)) (f1 (w + δ)) w := by
      have hc : HasDerivAt (f ∘ fun x => id x + δ) (f1 (w + δ) * 1) w :=
        (hf1 (w + δ)).comp w ((hasDerivAt_id w).add_const δ)
      exact hc.congr_deriv (mul_one _)
    exact (h1.fun_sub h2).congr_deriv (by dsimp [f1, h']; ring)
  have hh'_deriv : ∀ w, HasDerivAt h' (h'' w) w := by
    intro w
    have h1 : HasDerivAt (fun x => f1 (x - δ)) (f2 (w - δ)) w := by
      have hc : HasDerivAt (f1 ∘ fun x => id x - δ) (f2 (w - δ) * 1) w :=
        (hf2 (w - δ)).comp w ((hasDerivAt_id w).sub_const δ)
      exact hc.congr_deriv (mul_one _)
    have h2 : HasDerivAt (fun x => f1 (x + δ)) (f2 (w + δ)) w := by
      have hc : HasDerivAt (f1 ∘ fun x => id x + δ) (f2 (w + δ) * 1) w :=
        (hf2 (w + δ)).comp w ((hasDerivAt_id w).add_const δ)
      exact hc.congr_deriv (mul_one _)
    have heq_fn : h' = fun w => f1 (w - δ) - f1 (w + δ) := by ext x; dsimp [h', f1]; ring
    rw [heq_fn]; exact h1.fun_sub h2
  have hh''_deriv : ∀ w, HasDerivAt h'' (h''' w) w := by
    intro w
    have h1 : HasDerivAt (fun x => f2 (x - δ)) (f3 (w - δ)) w := by
      have hc : HasDerivAt (f2 ∘ fun x => id x - δ) (f3 (w - δ) * 1) w :=
        (hf3 (w - δ)).comp w ((hasDerivAt_id w).sub_const δ)
      exact hc.congr_deriv (mul_one _)
    have h2 : HasDerivAt (fun x => f2 (x + δ)) (f3 (w + δ)) w := by
      have hc : HasDerivAt (f2 ∘ fun x => id x + δ) (f3 (w + δ) * 1) w :=
        (hf3 (w + δ)).comp w ((hasDerivAt_id w).add_const δ)
      exact hc.congr_deriv (mul_one _)
    exact h1.fun_sub h2
  have hh'''_deriv : ∀ w, HasDerivAt h''' (h4 w) w := by
    intro w
    have h1 : HasDerivAt (fun x => f3 (x - δ)) (f4 (w - δ)) w := by
      have hc : HasDerivAt (f3 ∘ fun x => id x - δ) (f4 (w - δ) * 1) w :=
        (hf4 (w - δ)).comp w ((hasDerivAt_id w).sub_const δ)
      exact hc.congr_deriv (mul_one _)
    have h2 : HasDerivAt (fun x => f3 (x + δ)) (f4 (w + δ)) w := by
      have hc : HasDerivAt (f3 ∘ fun x => id x + δ) (f4 (w + δ) * 1) w :=
        (hf4 (w + δ)).comp w ((hasDerivAt_id w).add_const δ)
      exact hc.congr_deriv (mul_one _)
    exact h1.fun_sub h2
  have hh4_deriv : ∀ w, HasDerivAt h4 (h5 w) w := by
    intro w
    have h1 : HasDerivAt (fun x => f4 (x - δ)) (f5 (w - δ)) w := by
      have hc : HasDerivAt (f4 ∘ fun x => id x - δ) (f5 (w - δ) * 1) w :=
        (hf5 (w - δ)).comp w ((hasDerivAt_id w).sub_const δ)
      exact hc.congr_deriv (mul_one _)
    have h2 : HasDerivAt (fun x => f4 (x + δ)) (f5 (w + δ)) w := by
      have hc : HasDerivAt (f4 ∘ fun x => id x + δ) (f5 (w + δ) * 1) w :=
        (hf5 (w + δ)).comp w ((hasDerivAt_id w).add_const δ)
      exact hc.congr_deriv (mul_one _)
    exact h1.fun_sub h2
  have hc0 : Continuous h := continuous_iff_continuousAt.mpr fun w => (hh_deriv w).continuousAt
  have hc5 : Continuous h5 := by dsimp [h5, f5]; fun_prop
  have hp3 := P3_gauss_bounds a₀ δ t hδ ht
  have hsum_h : Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) := hp3.1
  refine ⟨hsum_h, ?_⟩
  let I_f6 : ℝ := 200 * t ^ 2 * √t
  have hfinite : ∀ N : ℕ, 1 ≤ N →
      |(∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k)) - (∫ w in a₀..(a₀ + N), h w) -
        (1 / 24) * (h' a₀ - h' (a₀ + N)) + (7 / 5760) * (h''' a₀ - h''' (a₀ + N))| ≤
        (1 / 4800) * (2 * δ) * I_f6 := by
    intro N _
    let rem : ℕ → ℝ := fun k =>
      (∫ r in (-1 / 2 : ℝ)..0, P5 r * h5 (a₀ + 1 / 2 + k + r)) +
        (∫ r in (0 : ℝ)..(1 / 2), P5 r * h5 (a₀ + 1 / 2 + k + r))
    have hsum_id : (∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k)) - (∫ w in a₀..(a₀ + N), h w) =
        (1 / 24) * (h' a₀ - h' (a₀ + N)) - (7 / 5760) * (h''' a₀ - h''' (a₀ + N)) -
          ∑ k ∈ Finset.range N, rem k := by
      have hidk : ∀ k : ℕ, h (a₀ + 1 / 2 + k) -
          (∫ w in (a₀ + k : ℝ)..(a₀ + (k + 1 : ℕ)), h w) =
          (1 / 24) * (h' (a₀ + k) - h' (a₀ + (k + 1 : ℕ))) -
            (7 / 5760) * (h''' (a₀ + k) - h''' (a₀ + (k + 1 : ℕ))) - rem k := by
        intro k
        have hcell := P5_cell_identity h h' h'' h''' h4 h5 (a₀ + 1 / 2 + k)
          hh_deriv hh'_deriv hh''_deriv hh'''_deriv hh4_deriv hc5
        have ha1 : a₀ + 1 / 2 + k - 1 / 2 = a₀ + k := by ring
        have ha2 : a₀ + 1 / 2 + k + 1 / 2 = a₀ + (k + 1 : ℕ) := by push_cast; ring
        rw [ha1, ha2] at hcell
        exact hcell
      have hsum_cell : ∑ k ∈ Finset.range N,
          (h (a₀ + 1 / 2 + k) - ∫ w in (a₀ + k : ℝ)..(a₀ + (k + 1 : ℕ)), h w) =
          ∑ k ∈ Finset.range N, ((1 / 24) * (h' (a₀ + k) - h' (a₀ + (k + 1 : ℕ))) -
            (7 / 5760) * (h''' (a₀ + k) - h''' (a₀ + (k + 1 : ℕ))) - rem k) :=
        Finset.sum_congr rfl fun k _ => hidk k
      conv_lhs at hsum_cell => rw [Finset.sum_sub_distrib]
      conv_rhs at hsum_cell => rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hteles_int : ∑ k ∈ Finset.range N, (∫ w in (a₀ + k : ℝ)..(a₀ + (k + 1 : ℕ)), h w) =
          ∫ w in a₀..(a₀ + N), h w := by
        have hgen : ∀ M : ℕ, ∑ k ∈ Finset.range M, (∫ w in (a₀ + k : ℝ)..(a₀ + (k + 1 : ℕ)), h w) =
            ∫ w in a₀..(a₀ + M), h w := by
          intro M
          induction M with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ, ih]
            by_cases hm : m = 0
            · subst hm; simp
            · exact intervalIntegral.integral_add_adjacent_intervals
                (hc0.intervalIntegrable a₀ (a₀ + m))
                (hc0.intervalIntegrable (a₀ + m) (a₀ + (m + 1 : ℕ)))
        exact hgen N
      have hteles_h' : ∑ k ∈ Finset.range N, (h' (a₀ + k) - h' (a₀ + (k + 1 : ℕ))) =
          h' a₀ - h' (a₀ + N) := by
        simpa using Finset.sum_range_sub' (fun k : ℕ => h' (a₀ + k)) N
      have hteles_h''' : ∑ k ∈ Finset.range N, (h''' (a₀ + k) - h''' (a₀ + (k + 1 : ℕ))) =
          h''' a₀ - h''' (a₀ + N) := by
        simpa using Finset.sum_range_sub' (fun k : ℕ => h''' (a₀ + k)) N
      rw [hteles_int, hteles_h', hteles_h'''] at hsum_cell
      exact hsum_cell
    have hdiff_eq : (∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k)) -
        (∫ w in a₀..(a₀ + N), h w) - (1 / 24) * (h' a₀ - h' (a₀ + N)) +
        (7 / 5760) * (h''' a₀ - h''' (a₀ + N)) = -∑ k ∈ Finset.range N, rem k := by
      linarith
    rw [hdiff_eq, abs_neg]
    have hh5_eq : ∀ w : ℝ, |h5 w| ≤ ∫ v in (-δ)..δ, |f6 (w + v)| := by
      intro w
      have hshift : ∀ v : ℝ, HasDerivAt (fun x => f5 (w + x)) (f6 (w + v)) v := by
        intro v
        exact ((hf6 (w + v)).comp v ((hasDerivAt_id v).const_add w)).congr_deriv (by simp)
      have hftc : ∫ v in (-δ)..δ, f6 (w + v) = f5 (w + δ) - f5 (w - δ) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hshift v)
          (Continuous.intervalIntegrable (by dsimp [f6]; fun_prop) _ _)]
        simp [sub_eq_add_neg]
      have hneg : h5 w = -(∫ v in (-δ)..δ, f6 (w + v)) := by
        rw [hftc]; dsimp [h5]; ring
      rw [hneg, abs_neg]
      exact intervalIntegral.abs_integral_le_integral_abs (by linarith : -δ ≤ δ)
    have hrem_le : ∀ k : ℕ, |rem k| ≤
        (1 / 4800) * ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)| := by
      intro k
      have hcont_inner : Continuous (fun r : ℝ => ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)|) := by
        have hcont2 : Continuous (fun p : ℝ × ℝ => |f6 (a₀ + 1 / 2 + k + p.1 + p.2)|) := by
          dsimp [f6]; fun_prop
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont2 (-δ) δ
      have hhalf_le : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) → b ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) →
          |∫ r in a..b, P5 r * h5 (a₀ + 1 / 2 + k + r)| ≤
            (1 / 4800) * ∫ r in a..b, ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)| := by
        intro a b hab ha hb
        refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
        have hi1 : IntervalIntegrable (fun r => |P5 r * h5 (a₀ + 1 / 2 + k + r)|) volume a b :=
          ((continuous_P5.mul (hc5.comp (continuous_const.add continuous_id))).abs).intervalIntegrable a b
        have hi2 : IntervalIntegrable (fun r => (1 / 4800 : ℝ) * ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)|) volume a b :=
          (continuous_const.mul hcont_inner).intervalIntegrable a b
        have hmono := intervalIntegral.integral_mono_on hab hi1 hi2 fun r hr => ?_
        · rw [intervalIntegral.integral_const_mul] at hmono
          exact hmono
        · rw [abs_mul]
          have hr1 : -1 / 2 ≤ r := le_trans ha.1 hr.1
          have hr2 : r ≤ 1 / 2 := le_trans hr.2 hb.2
          exact mul_le_mul (abs_P5_le hr1 hr2) (hh5_eq _) (abs_nonneg _) (by norm_num)
      have hL := hhalf_le (-1 / 2) 0 (by norm_num) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      have hR := hhalf_le 0 (1 / 2) (by norm_num) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, le_rfl⟩
      have hsplit : ∫ r in (-1 / 2 : ℝ)..(1 / 2), (∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)|) =
          (∫ r in (-1 / 2 : ℝ)..0, ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)|) +
          (∫ r in (0 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)|) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_inner.intervalIntegrable _ _) (hcont_inner.intervalIntegrable _ _)).symm
      calc |rem k| ≤ |∫ r in (-1 / 2 : ℝ)..0, P5 r * h5 (a₀ + 1 / 2 + k + r)| +
            |∫ r in (0 : ℝ)..(1 / 2), P5 r * h5 (a₀ + 1 / 2 + k + r)| := abs_add_le _ _
        _ ≤ _ := add_le_add hL hR
        _ = (1 / 4800) * ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)| := by
            rw [hsplit]; ring
    have hsum_rem : |∑ k ∈ Finset.range N, rem k| ≤ (1 / 4800) * (2 * δ) * I_f6 := by
      have h1 : |∑ k ∈ Finset.range N, rem k| ≤ ∑ k ∈ Finset.range N, |rem k| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ k ∈ Finset.range N, |rem k| ≤ (1 / 4800) * ∑ k ∈ Finset.range N,
          ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)| := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => hrem_le k
      have hswap_k : ∀ k : ℕ,
          ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)| =
          ∫ v in (-δ)..δ, ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u| := by
        intro k
        have hcont2 : Continuous (fun p : ℝ × ℝ => |f6 (a₀ + 1 / 2 + k + p.1 + p.2)|) := by
          dsimp [f6]; fun_prop
        have hint_prod : Integrable (fun p : ℝ × ℝ => |f6 (a₀ + 1 / 2 + k + p.1 + p.2)|)
            ((volume.restrict (Set.Ioc (-1 / 2 : ℝ) (1 / 2))).prod (volume.restrict (Set.Ioc (-δ) δ))) := by
          rw [Measure.prod_restrict]
          refine (hcont2.continuousOn.integrableOn_Icc (a := (-1 / 2, -δ)) (b := (1 / 2, δ))).mono_set ?_
          intro p hp
          exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2, hp.2.2⟩⟩
        rw [intervalIntegral.integral_of_le (by norm_num)]
        simp_rw [intervalIntegral.integral_of_le (by linarith : -δ ≤ δ)]
        rw [MeasureTheory.integral_integral_swap hint_prod]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
        rw [← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
        have hcomp := intervalIntegral.integral_comp_add_left (fun u => |f6 u|)
          (a₀ + 1 / 2 + k + v) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        have hpt : (fun r => |f6 (a₀ + 1 / 2 + k + r + v)|) =
            (fun r => |f6 (a₀ + 1 / 2 + k + v + r)|) := by
          ext r; ring_nf
        rw [hpt]
        convert hcomp using 2 <;> push_cast <;> ring
      have hc_v : ∀ k : ℕ, Continuous (fun v : ℝ =>
          ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u|) := by
        intro k
        have hsub : ∀ v, ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u| =
            ∫ w in (0 : ℝ)..1, |f6 (a₀ + k + v + w)| := by
          intro v
          have hcomp := intervalIntegral.integral_comp_add_left (fun u => |f6 u|) (a₀ + k + v)
            (a := (0 : ℝ)) (b := (1 : ℝ))
          have hb_eq : a₀ + (k + 1 : ℕ) + v = a₀ + k + v + 1 := by push_cast; ring
          rw [add_zero, ← hb_eq] at hcomp
          exact hcomp.symm
        simp_rw [hsub]
        have hcont_vw : Continuous (fun p : ℝ × ℝ => |f6 (a₀ + k + p.1 + p.2)|) := by
          dsimp [f6]; fun_prop
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont_vw 0 1
      have hsum_swap : ∑ k ∈ Finset.range N,
          ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)| =
          ∫ v in (-δ)..δ, ∑ k ∈ Finset.range N,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u| := by
        simp_rw [hswap_k]
        rw [← intervalIntegral.integral_finsetSum]
        intro k _
        exact (hc_v k).intervalIntegrable (-δ) δ
      have htele_f6 : ∀ v, ∑ k ∈ Finset.range N,
          ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u| ≤ I_f6 := by
        intro v
        have hsum_eq : ∀ M : ℕ, ∑ k ∈ Finset.range M,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u| =
            ∫ u in (a₀ + v)..(a₀ + M + v), |f6 u| := by
          intro M
          induction M with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ, ih]
            have hc_abs : Continuous (fun u => |f6 u|) := by dsimp [f6]; fun_prop
            exact intervalIntegral.integral_add_adjacent_intervals
              (hc_abs.intervalIntegrable _ _) (hc_abs.intervalIntegrable _ _)
        rw [hsum_eq N]
        exact f_sixth_integral_bound (a₀ + v) (a₀ + N + v) t ht (by linarith)
      have hint_ub : ∫ v in (-δ)..δ, ∑ k ∈ Finset.range N,
          ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u| ≤ (2 * δ) * I_f6 := by
        have hc_sum : IntervalIntegrable (fun v => ∑ k ∈ Finset.range N,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u|) volume (-δ) δ :=
          (continuous_finsetSum _ fun k _ => hc_v k).intervalIntegrable (-δ) δ
        have hm := intervalIntegral.integral_mono_on (by linarith : -δ ≤ δ) hc_sum
          intervalIntegrable_const (fun v _ => htele_f6 v)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
        linarith
      calc |∑ k ∈ Finset.range N, rem k|
          ≤ ∑ k ∈ Finset.range N, |rem k| := h1
        _ ≤ (1 / 4800) * ∑ k ∈ Finset.range N,
            ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f6 (a₀ + 1 / 2 + k + r + v)| := h2
        _ = (1 / 4800) * ∫ v in (-δ)..δ, ∑ k ∈ Finset.range N,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f6 u| := by rw [hsum_swap]
        _ ≤ (1 / 4800) * ((2 * δ) * I_f6) := mul_le_mul_of_nonneg_left hint_ub (by norm_num)
        _ = (1 / 4800) * (2 * δ) * I_f6 := by ring
    exact hsum_rem
  have htend_sum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k))
      atTop (𝓝 (∑' k : ℕ, h (a₀ + 1 / 2 + k))) :=
    hsum_h.hasSum.tendsto_sum_nat
  have htend_poly_exp : ∀ (d : ℕ) (c : ℝ),
      Tendsto (fun N : ℕ => (a₀ + (N : ℝ) + c) ^ d * Real.exp (-(a₀ + (N : ℝ) + c) ^ 2 * t))
        atTop (𝓝 0) := by
    intro d c
    have harg : Tendsto (fun N : ℕ => a₀ + (N : ℝ) + c) atTop atTop :=
      (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds
    have h0 : Tendsto (fun u : ℝ => u ^ d * Real.exp (-t * u ^ 2)) atTop (𝓝 0) := by
      have hb : ∀ᶠ u : ℝ in atTop, u ^ d * Real.exp (-t * u ^ 2) ∈
          Set.Icc 0 (((d + 1).factorial : ℝ) / t ^ (d + 1) * u⁻¹) := by
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
        have hu0 : 0 < u := by linarith
        refine ⟨mul_nonneg (pow_nonneg hu0.le d) (Real.exp_pos _).le, ?_⟩
        have htu0 : 0 ≤ t * u ^ 2 := by positivity
        have hexp_lb : (t * u ^ 2) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤ Real.exp (t * u ^ 2) := by
          have hs := Real.sum_le_exp_of_nonneg htu0 (d + 2)
          have hterm : (t * u ^ 2) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤
              ∑ k ∈ Finset.range (d + 2), (t * u ^ 2) ^ k / (k.factorial : ℝ) :=
            Finset.single_le_sum (f := fun k : ℕ => (t * u ^ 2) ^ k / (k.factorial : ℝ))
              (fun k _ => by positivity) (Finset.mem_range.mpr (by omega))
          exact hterm.trans hs
        have hpow_pos : 0 < (t * u ^ 2) ^ (d + 1) / ((d + 1).factorial : ℝ) := by positivity
        have hinv : Real.exp (-t * u ^ 2) ≤ ((d + 1).factorial : ℝ) / (t * u ^ 2) ^ (d + 1) := by
          rw [show -t * u ^ 2 = -(t * u ^ 2) by ring, Real.exp_neg]
          simpa [one_div, inv_div] using inv_anti₀ hpow_pos hexp_lb
        have hu_pow : u ^ d ≤ u ^ (2 * d + 1) :=
          pow_le_pow_right₀ hu.le (by omega)
        calc u ^ d * Real.exp (-t * u ^ 2)
            ≤ u ^ d * (((d + 1).factorial : ℝ) / (t * u ^ 2) ^ (d + 1)) :=
              mul_le_mul_of_nonneg_left hinv (pow_nonneg hu0.le d)
          _ = ((d + 1).factorial : ℝ) / t ^ (d + 1) * (u ^ d / u ^ (2 * d + 2)) := by
              rw [mul_pow, ← pow_mul]; ring
          _ ≤ ((d + 1).factorial : ℝ) / t ^ (d + 1) * (u ^ (2 * d + 1) / u ^ (2 * d + 2)) := by
              have hdiv : u ^ d / u ^ (2 * d + 2) ≤ u ^ (2 * d + 1) / u ^ (2 * d + 2) :=
                div_le_div_of_nonneg_right hu_pow (by positivity)
              exact mul_le_mul_of_nonneg_left hdiv (by positivity)
          _ = ((d + 1).factorial : ℝ) / t ^ (d + 1) * u⁻¹ := by
              rw [show u ^ (2 * d + 2) = u ^ (2 * d + 1) * u from by ring]
              field_simp
      have htend_inv : Tendsto (fun u : ℝ => ((d + 1).factorial : ℝ) / t ^ (d + 1) * u⁻¹) atTop (𝓝 0) := by
        have hzero : ((d + 1).factorial : ℝ) / t ^ (d + 1) * 0 = 0 := mul_zero _
        rw [← hzero]
        exact tendsto_inv_atTop_zero.const_mul _
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend_inv
        (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
    refine (h0.comp harg).congr fun N => ?_
    dsimp; ring_nf
  have htend_h' : Tendsto (fun N : ℕ => h' (a₀ + N)) atTop (𝓝 0) := by
    have h1 := ((htend_poly_exp 1 (-δ)).const_mul (-2 * t)).add ((htend_poly_exp 1 δ).const_mul (2 * t))
    simpa [pow_one, mul_zero, add_zero] using h1.congr fun N => by dsimp [h']; ring
  have htend_h''' : Tendsto (fun N : ℕ => h''' (a₀ + N)) atTop (𝓝 0) := by
    have ht1 : Tendsto (fun N : ℕ => f3 (a₀ + N - δ)) atTop (𝓝 0) := by
      have hc := ((htend_poly_exp 3 (-δ)).const_mul (-8 * t ^ 3)).add
        ((htend_poly_exp 1 (-δ)).const_mul (12 * t ^ 2))
      simpa [pow_one, mul_zero, add_zero] using hc.congr fun N => by dsimp [f3]; ring
    have ht2 : Tendsto (fun N : ℕ => f3 (a₀ + N + δ)) atTop (𝓝 0) := by
      have hc := ((htend_poly_exp 3 δ).const_mul (-8 * t ^ 3)).add
        ((htend_poly_exp 1 δ).const_mul (12 * t ^ 2))
      simpa [pow_one, mul_zero, add_zero] using hc.congr fun N => by dsimp [f3]; ring
    simpa [sub_zero] using ht1.sub ht2
  have htend_int : Tendsto (fun N : ℕ => ∫ w in a₀..(a₀ + N), h w) atTop
      (𝓝 (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t))) := by
    have heq : ∀ N : ℕ, ∫ w in a₀..(a₀ + N), h w =
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) -
          ∫ v in (a₀ + N - δ)..(a₀ + N + δ), Real.exp (-v ^ 2 * t) := by
      intro N
      have hf_cont : Continuous f := by dsimp [f]; fun_prop
      have h1 : ∫ w in a₀..(a₀ + N), f (w - δ) = ∫ v in (a₀ - δ)..(a₀ + N - δ), f v := by
        simp [sub_eq_add_neg]
      have h2 : ∫ w in a₀..(a₀ + N), f (w + δ) = ∫ v in (a₀ + δ)..(a₀ + N + δ), f v := by
        simp
      have hsub0 : ∫ w in a₀..(a₀ + N), h w =
          (∫ w in a₀..(a₀ + N), f (w - δ)) - (∫ w in a₀..(a₀ + N), f (w + δ)) :=
        intervalIntegral.integral_sub
          ((hf_cont.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)
          ((hf_cont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
      have hsub : ∫ w in a₀..(a₀ + N), h w =
          (∫ v in (a₀ - δ)..(a₀ + N - δ), f v) - (∫ v in (a₀ + δ)..(a₀ + N + δ), f v) := by
        rw [hsub0, h1, h2]
      have hid1 : ∫ v in (a₀ - δ)..(a₀ + N - δ), f v =
          (∫ v in (a₀ - δ)..(a₀ + δ), f v) + (∫ v in (a₀ + δ)..(a₀ + N - δ), f v) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hf_cont.intervalIntegrable _ _) (hf_cont.intervalIntegrable _ _)).symm
      have hid2 : ∫ v in (a₀ + δ)..(a₀ + N + δ), f v =
          (∫ v in (a₀ + δ)..(a₀ + N - δ), f v) + (∫ v in (a₀ + N - δ)..(a₀ + N + δ), f v) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hf_cont.intervalIntegrable _ _) (hf_cont.intervalIntegrable _ _)).symm
      rw [hsub, hid1, hid2]; ring
    simp_rw [heq]
    have htail : Tendsto (fun N : ℕ => ∫ v in (a₀ + N - δ)..(a₀ + N + δ), f v) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      have hbound : ∀ᶠ N : ℕ in atTop,
          ‖∫ v in (a₀ + N - δ)..(a₀ + N + δ), f v‖ ≤ (2 * δ) * Real.exp (-(a₀ + N - δ) ^ 2 * t) := by
        filter_upwards [eventually_ge_atTop (Nat.ceil (max 0 (δ - a₀)) + 1)] with N hN
        have hpos_left : 0 ≤ a₀ + N - δ := by
          have h1 : max 0 (δ - a₀) ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : Nat.ceil (max 0 (δ - a₀)) ≤ N))
          linarith [le_max_right (0 : ℝ) (δ - a₀)]
        have hi := intervalIntegral.integral_mono_on (by linarith : a₀ + N - δ ≤ a₀ + N + δ)
          ((by dsimp [f]; fun_prop : Continuous f).intervalIntegrable (μ := volume) _ _)
          (intervalIntegrable_const (c := Real.exp (-(a₀ + (N : ℝ) - δ) ^ 2 * t))) fun v hv => by
            dsimp [f]
            have hsq : (a₀ + (N : ℝ) - δ) ^ 2 ≤ v ^ 2 := by nlinarith [hv.1, hpos_left]
            exact Real.exp_le_exp.mpr (by nlinarith [hsq, ht])
        have hnonneg : 0 ≤ ∫ v in (a₀ + N - δ)..(a₀ + N + δ), f v :=
          intervalIntegral.integral_nonneg (by linarith) fun v _ => (Real.exp_pos _).le
        rw [Real.norm_of_nonneg hnonneg]
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
        linarith
      have htend_exp : Tendsto (fun N : ℕ => (2 * δ) * Real.exp (-(a₀ + N - δ) ^ 2 * t)) atTop (𝓝 0) := by
        have harg : Tendsto (fun N : ℕ => -(a₀ + (N : ℝ) - δ) ^ 2 * t) atTop atBot := by
          have hnat : Tendsto (fun N : ℕ => a₀ + (N : ℝ) - δ) atTop atTop :=
            (((tendsto_const_nhds (x := a₀)).add_atTop tendsto_natCast_atTop_atTop).atTop_add
              (tendsto_const_nhds (x := -δ))).congr fun N => by ring
          have hsq : Tendsto (fun u : ℝ => -u ^ 2 * t) atTop atBot :=
            (tendsto_neg_atTop_atBot.comp
              ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_mul_const ht)).congr fun u => by
              dsimp [Function.comp_def]; ring
          exact hsq.comp hnat
        have hzero : (2 * δ : ℝ) * 0 = 0 := mul_zero _
        rw [← hzero]
        exact (tendsto_exp_atBot.comp harg).const_mul (2 * δ)
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound htend_exp
    simpa only [sub_zero] using (tendsto_const_nhds (x := ∫ v in (a₀ - δ)..(a₀ + δ), f v)).sub htail
  have htend_lhs : Tendsto (fun N : ℕ =>
      |(∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k)) -
        (∫ w in a₀..(a₀ + N), h w) -
        (1 / 24) * (h' a₀ - h' (a₀ + N)) +
        (7 / 5760) * (h''' a₀ - h''' (a₀ + N))|) atTop
      (𝓝 |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀ +
        (7 / 5760) * h''' a₀|) := by
    simpa only [sub_zero] using (((htend_sum.sub htend_int).sub
      (((tendsto_const_nhds (x := h' a₀)).sub htend_h').const_mul (1 / 24 : ℝ))).add
      (((tendsto_const_nhds (x := h''' a₀)).sub htend_h''').const_mul (7 / 5760 : ℝ))).abs
  have hle_lim : |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
      (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀ +
      (7 / 5760) * h''' a₀| ≤ (1 / 4800) * (2 * δ) * I_f6 :=
    le_of_tendsto htend_lhs (by filter_upwards [eventually_ge_atTop 1] with N hN; exact hfinite N hN)
  have hconst : (1 / 4800 : ℝ) * (2 * δ) * I_f6 = (1 / 24) * (2 * δ) * t ^ 2 * √t := by
    dsimp [I_f6]; ring
  linarith [hle_lim, hconst]


lemma p5_aux (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) +
        2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * u * (2 * u ^ 2 * t - 3) * Real.exp (-u ^ 2 * t)
    let h''' : ℝ → ℝ := fun w => f3 (w - δ) - f3 (w + δ)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
    |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) - (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) -
      (1 / 24) * h' a₀ + (7 / 5760) * h''' a₀| ≤ (1 / 24) * (2 * δ) * t ^ 2 * √t := P5_gauss_bounds a₀ δ t hδ ht

end SolGammaHelpers

theorem solution (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) +
        2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * u * (2 * u ^ 2 * t - 3) * Real.exp (-u ^ 2 * t)
    let h''' : ℝ → ℝ := fun w => f3 (w - δ) - f3 (w + δ)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
    |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) - (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) -
      (1 / 24) * h' a₀ + (7 / 5760) * h''' a₀| ≤ (1 / 24) * (2 * δ) * t ^ 2 * √t :=
  SolGammaHelpers.p5_aux a₀ δ t hδ ht
