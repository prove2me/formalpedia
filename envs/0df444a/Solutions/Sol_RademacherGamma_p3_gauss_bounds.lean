-- Prove2me | solution 1 for RademacherGamma_p3_gauss_bounds
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:51:12.018172+00:00
-- url     : https://prove2.me/submissions/2e9b5477-09be-4a37-9713-4a70704f4e87

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace SolGammaHelpers

open Real MeasureTheory Filter Set
open scoped Topology

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

private lemma phi3_nonneg_integral_le (M : ℝ) (_hM : 0 ≤ M) :
    ∫ z in (0 : ℝ)..M, |4 * (4 * z ^ 4 - 12 * z ^ 2 + 3) * Real.exp (-z ^ 2)| ≤ 113 / 10 := by
  let G : ℝ → ℝ := fun z => |4 * (4 * z ^ 4 - 12 * z ^ 2 + 3) * Real.exp (-z ^ 2)|
  let phi2 : ℝ → ℝ := fun z => 4 * z * (2 * z ^ 2 - 3) * Real.exp (-z ^ 2)
  let phi3 : ℝ → ℝ := fun z => 4 * (4 * z ^ 4 - 12 * z ^ 2 + 3) * Real.exp (-z ^ 2)
  have hG_cont : Continuous G := by fun_prop
  have hphi2_deriv : ∀ z : ℝ, HasDerivAt phi2 (-phi3 z) z := by
    intro z
    have hpoly : HasDerivAt (fun x : ℝ => 4 * x * (2 * x ^ 2 - 3)) (24 * z ^ 2 - 12) z := by
      have h1 : HasDerivAt (fun x : ℝ => 4 * x) 4 z := by
        simpa using (hasDerivAt_id z).const_mul 4
      have h2 : HasDerivAt (fun x : ℝ => 2 * x ^ 2 - 3) (4 * z) z := by
        have hp := (hasDerivAt_pow 2 z).const_mul 2
        exact (hp.fun_sub (hasDerivAt_const z (3 : ℝ))).congr_deriv (by ring)
      exact (h1.fun_mul h2).congr_deriv (by ring)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2)) (-2 * z * Real.exp (-z ^ 2)) z := by
      have hsq : HasDerivAt (fun x : ℝ => -x ^ 2) (-2 * z) z :=
        ((hasDerivAt_pow 2 z).fun_neg).congr_deriv (by ring)
      convert hsq.exp using 1; ring
    exact (hpoly.fun_mul hexp).congr_deriv (by dsimp [phi3]; ring)
  set M' := max M (5 / 3)
  have hMM' : M ≤ M' := le_max_left _ _
  have hM'_ge : 5 / 3 ≤ M' := le_max_right _ _
  have hsplit0 : ∫ z in (0 : ℝ)..M', G z =
      (∫ z in (0 : ℝ)..M, G z) + (∫ z in M..M', G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hnonneg_tail : 0 ≤ ∫ z in M..M', G z :=
    intervalIntegral.integral_nonneg hMM' fun z _ => abs_nonneg _
  have hle_M' : ∫ z in (0 : ℝ)..M, G z ≤ ∫ z in (0 : ℝ)..M', G z := by
    linarith only [hsplit0, hnonneg_tail]
  have hsplit1 : ∫ z in (0 : ℝ)..M', G z =
      (∫ z in (0 : ℝ)..(1 / 2), G z) + (∫ z in (1 / 2 : ℝ)..M', G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hsplit2 : ∫ z in (1 / 2 : ℝ)..M', G z =
      (∫ z in (1 / 2 : ℝ)..(3 / 5), G z) + (∫ z in (3 / 5 : ℝ)..M', G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hsplit3 : ∫ z in (3 / 5 : ℝ)..M', G z =
      (∫ z in (3 / 5 : ℝ)..(3 / 2), G z) + (∫ z in (3 / 2 : ℝ)..M', G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hsplit4 : ∫ z in (3 / 2 : ℝ)..M', G z =
      (∫ z in (3 / 2 : ℝ)..(5 / 3), G z) + (∫ z in (5 / 3 : ℝ)..M', G z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable _ _) (hG_cont.intervalIntegrable _ _)).symm
  have hexp_q1 : Real.exp (-(1 / 4 : ℝ)) ≤ 384 / 493 :=
    exp_neg_ub_of_le (by norm_num) le_rfl (by norm_num) (by norm_num)
  have hexp_q2 : Real.exp (-(9 / 4 : ℝ)) ≤ 128 / 983 :=
    exp_neg_ub_of_le (by norm_num) le_rfl (by norm_num) (by norm_num)
  have hexp_q3 : Real.exp (-(9 / 25 : ℝ)) ≤ 15625 / 22384 :=
    exp_neg_ub_of_le (by norm_num) le_rfl (by norm_num) (by norm_num)
  have hexp_q4 : Real.exp (-(25 / 9 : ℝ)) ≤ 2187 / 24512 :=
    exp_neg_ub_of_le (by norm_num) le_rfl (by norm_num) (by norm_num)
  -- Piece 1: [0, 1/2]
  have hb1 : ∫ z in (0 : ℝ)..(1 / 2), G z ≤ 39 / 10 := by
    have heq : ∫ z in (0 : ℝ)..(1 / 2), G z = ∫ z in (0 : ℝ)..(1 / 2), phi3 z := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hz
      have hz2 : z ^ 2 ≤ 1 / 4 := by nlinarith [hz.1, hz.2]
      have hpos : 0 ≤ 4 * z ^ 4 - 12 * z ^ 2 + 3 := by
        have hz4 : 0 ≤ z ^ 4 := by positivity
        nlinarith [hz2, hz4]
      exact abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    rw [heq]
    have hftc : ∫ z in (0 : ℝ)..(1 / 2), phi3 z = phi2 0 - phi2 (1 / 2) := by
      have h_neg := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hphi2_deriv z)
        (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) (1 / 2))
      linarith [show ∫ z in (0 : ℝ)..(1 / 2), -phi3 z = -∫ z in (0 : ℝ)..(1 / 2), phi3 z from
        intervalIntegral.integral_neg]
    rw [hftc]
    have hval : phi2 0 - phi2 (1 / 2) = 5 * Real.exp (-(1 / 4 : ℝ)) := by
      dsimp [phi2]; norm_num
    rw [hval]
    have hm := mul_le_mul_of_nonneg_left hexp_q1 (by norm_num : (0 : ℝ) ≤ 5)
    linarith only [hm]
  -- Piece 2: [1/2, 3/5]
  have hb2 : ∫ z in (1 / 2 : ℝ)..(3 / 5), G z ≤ 32 / 100 := by
    have hpt : ∀ z ∈ Set.Icc (1 / 2 : ℝ) (3 / 5), G z ≤ 4 * (384 / 493) := by
      intro z hz
      have hz2_lo : 1 / 4 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hz2_hi : z ^ 2 ≤ 9 / 25 := by nlinarith only [hz.1, hz.2]
      have hsq : 4 * z ^ 4 - 12 * z ^ 2 + 3 = 4 * (z ^ 2 - 3 / 2) ^ 2 - 6 := by ring
      have hbd1 : -(5 / 4 : ℝ) ≤ z ^ 2 - 3 / 2 := by linarith only [hz2_lo]
      have hbd2 : z ^ 2 - 3 / 2 ≤ -(57 / 50 : ℝ) := by linarith only [hz2_hi]
      have hsq_lo : (57 / 50 : ℝ) ^ 2 ≤ (z ^ 2 - 3 / 2) ^ 2 := by nlinarith only [hbd2]
      have hsq_hi : (z ^ 2 - 3 / 2) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by nlinarith only [hbd1, hbd2]
      have h1 : -1 ≤ 4 * z ^ 4 - 12 * z ^ 2 + 3 := by linarith only [hsq, hsq_lo]
      have h2 : 4 * z ^ 4 - 12 * z ^ 2 + 3 ≤ 1 := by linarith only [hsq, hsq_hi]
      have habs : |4 * z ^ 4 - 12 * z ^ 2 + 3| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
      have hexp : Real.exp (-z ^ 2) ≤ 384 / 493 := by
        calc Real.exp (-z ^ 2) ≤ Real.exp (-(1 / 4 : ℝ)) :=
              Real.exp_le_exp.mpr (by linarith only [hz2_lo])
          _ ≤ 384 / 493 := hexp_q1
      dsimp [G]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_pos (Real.exp_pos _)]
      have hm := mul_le_mul habs hexp (Real.exp_pos _).le (by norm_num)
      linarith only [hm]
    have hi := intervalIntegral.integral_mono_on (by norm_num)
      (hG_cont.intervalIntegrable (μ := volume) _ _)
      (intervalIntegrable_const (c := (4 : ℝ) * (384 / 493))) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    linarith only [hi]
  -- Piece 3: [3/5, 3/2]
  have hb3 : ∫ z in (3 / 5 : ℝ)..(3 / 2), G z ≤ 501 / 100 := by
    have heq : ∫ z in (3 / 5 : ℝ)..(3 / 2), G z = ∫ z in (3 / 5 : ℝ)..(3 / 2), -phi3 z := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hz
      have hz2_lo : 9 / 25 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hz2_hi : z ^ 2 ≤ 9 / 4 := by nlinarith only [hz.1, hz.2]
      have hsq : 4 * z ^ 4 - 12 * z ^ 2 + 3 = 4 * (z ^ 2 - 3 / 2) ^ 2 - 6 := by ring
      have hbd1 : -(57 / 50 : ℝ) ≤ z ^ 2 - 3 / 2 := by linarith only [hz2_lo]
      have hbd2 : z ^ 2 - 3 / 2 ≤ 3 / 4 := by linarith only [hz2_hi]
      have hsq_hi : (z ^ 2 - 3 / 2) ^ 2 ≤ (57 / 50 : ℝ) ^ 2 := by nlinarith only [hbd1, hbd2]
      have hneg : 4 * z ^ 4 - 12 * z ^ 2 + 3 ≤ 0 := by linarith only [hsq, hsq_hi]
      have hle0 : phi3 z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith only [hneg]) (Real.exp_pos _).le
      exact abs_of_nonpos hle0
    rw [heq]
    have hftc : ∫ z in (3 / 5 : ℝ)..(3 / 2), -phi3 z = phi2 (3 / 2) - phi2 (3 / 5) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hphi2_deriv z)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [hftc]
    have hval : phi2 (3 / 2) - phi2 (3 / 5) =
        9 * Real.exp (-(9 / 4 : ℝ)) + (684 / 125 : ℝ) * Real.exp (-(9 / 25 : ℝ)) := by
      dsimp [phi2]; norm_num
    rw [hval]
    have hm2 := mul_le_mul_of_nonneg_left hexp_q2 (by norm_num : (0 : ℝ) ≤ 9)
    have hm3 := mul_le_mul_of_nonneg_left hexp_q3 (by norm_num : (0 : ℝ) ≤ 684 / 125)
    linarith only [hm2, hm3]
  -- Piece 4: [3/2, 5/3]
  have hb4 : ∫ z in (3 / 2 : ℝ)..(5 / 3), G z ≤ 53 / 100 := by
    have hpt : ∀ z ∈ Set.Icc (3 / 2 : ℝ) (5 / 3), G z ≤ 24 * (128 / 983) := by
      intro z hz
      have hz2_lo : 9 / 4 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hz2_hi : z ^ 2 ≤ 25 / 9 := by nlinarith only [hz.1, hz.2]
      have hsq : 4 * z ^ 4 - 12 * z ^ 2 + 3 = 4 * (z ^ 2 - 3 / 2) ^ 2 - 6 := by ring
      have hbd1 : 3 / 4 ≤ z ^ 2 - 3 / 2 := by linarith only [hz2_lo]
      have hbd2 : z ^ 2 - 3 / 2 ≤ 23 / 18 := by linarith only [hz2_hi]
      have hsq_lo : (3 / 4 : ℝ) ^ 2 ≤ (z ^ 2 - 3 / 2) ^ 2 := by nlinarith only [hbd1]
      have hsq_hi : (z ^ 2 - 3 / 2) ^ 2 ≤ (23 / 18 : ℝ) ^ 2 := by nlinarith only [hbd1, hbd2]
      have h1 : -6 ≤ 4 * z ^ 4 - 12 * z ^ 2 + 3 := by linarith only [hsq, hsq_lo]
      have h2 : 4 * z ^ 4 - 12 * z ^ 2 + 3 ≤ 6 := by linarith only [hsq, hsq_hi]
      have habs : |4 * z ^ 4 - 12 * z ^ 2 + 3| ≤ 6 := abs_le.mpr ⟨h1, h2⟩
      have hexp : Real.exp (-z ^ 2) ≤ 128 / 983 := by
        calc Real.exp (-z ^ 2) ≤ Real.exp (-(9 / 4 : ℝ)) :=
              Real.exp_le_exp.mpr (by linarith only [hz2_lo])
          _ ≤ 128 / 983 := hexp_q2
      dsimp [G]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_pos (Real.exp_pos _)]
      have hm := mul_le_mul habs hexp (Real.exp_pos _).le (by norm_num)
      linarith only [hm]
    have hi := intervalIntegral.integral_mono_on (by norm_num)
      (hG_cont.intervalIntegrable (μ := volume) _ _)
      (intervalIntegrable_const (c := (24 : ℝ) * (128 / 983))) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    linarith only [hi]
  -- Piece 5: [5/3, M']
  have hb5 : ∫ z in (5 / 3 : ℝ)..M', G z ≤ 154 / 100 := by
    have heq : ∫ z in (5 / 3 : ℝ)..M', G z = ∫ z in (5 / 3 : ℝ)..M', phi3 z := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [Set.uIcc_of_le hM'_ge] at hz
      have hz2_lo : 25 / 9 ≤ z ^ 2 := by nlinarith only [hz.1]
      have hsq : 4 * z ^ 4 - 12 * z ^ 2 + 3 = 4 * (z ^ 2 - 3 / 2) ^ 2 - 6 := by ring
      have hbd1 : 23 / 18 ≤ z ^ 2 - 3 / 2 := by linarith only [hz2_lo]
      have hsq_lo : (23 / 18 : ℝ) ^ 2 ≤ (z ^ 2 - 3 / 2) ^ 2 := by nlinarith only [hbd1]
      have hpos : 0 ≤ 4 * z ^ 4 - 12 * z ^ 2 + 3 := by linarith only [hsq, hsq_lo]
      exact abs_of_nonneg (mul_nonneg (by linarith only [hpos]) (Real.exp_pos _).le)
    rw [heq]
    have hftc : ∫ z in (5 / 3 : ℝ)..M', phi3 z = phi2 (5 / 3) - phi2 M' := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hphi2_deriv z)
        (Continuous.intervalIntegrable (by fun_prop) (5 / 3 : ℝ) M')
      linarith only [this, show ∫ z in (5 / 3 : ℝ)..M', -phi3 z = -∫ z in (5 / 3 : ℝ)..M', phi3 z from
        intervalIntegral.integral_neg]
    rw [hftc]
    have hphi2_nonneg : 0 ≤ phi2 M' := by
      dsimp [phi2]
      have h2m : 0 ≤ 2 * M' ^ 2 - 3 := by nlinarith only [hM'_ge]
      positivity
    have hval : phi2 (5 / 3) = (460 / 27 : ℝ) * Real.exp (-(25 / 9 : ℝ)) := by
      dsimp [phi2]; norm_num
    have hm4 := mul_le_mul_of_nonneg_left hexp_q4 (by norm_num : (0 : ℝ) ≤ 460 / 27)
    linarith only [hphi2_nonneg, hval, hm4]
  linarith only [hle_M', hsplit1, hsplit2, hsplit3, hsplit4, hb1, hb2, hb3, hb4, hb5]

private lemma phi3_integral_bound (a b : ℝ) (_hab : a ≤ b) :
    ∫ z in a..b, |4 * (4 * z ^ 4 - 12 * z ^ 2 + 3) * Real.exp (-z ^ 2)| ≤ 113 / 5 := by
  let G : ℝ → ℝ := fun z => |4 * (4 * z ^ 4 - 12 * z ^ 2 + 3) * Real.exp (-z ^ 2)|
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
  have hhalf := phi3_nonneg_integral_le M hM0
  linarith

private lemma f_fourth_integral_bound (a b t : ℝ) (ht : 0 < t) (hab : a ≤ b) :
    ∫ u in a..b, |4 * t ^ 2 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)| ≤
      (113 / 5) * t * √t := by
  let G : ℝ → ℝ := fun z => |4 * (4 * z ^ 4 - 12 * z ^ 2 + 3) * Real.exp (-z ^ 2)|
  have hsqrt : 0 < √t := Real.sqrt_pos.mpr ht
  have hsq : √t ^ 2 = t := Real.sq_sqrt ht.le
  have hcomp := intervalIntegral.integral_comp_mul_left G hsqrt.ne' (a := a) (b := b)
  have heq : ∫ u in a..b, |4 * t ^ 2 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)| =
      t * √t * ∫ z in (√t * a)..(√t * b), G z := by
    have hpt : (fun u => |4 * t ^ 2 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)|) =
        (fun u => t ^ 2 * G (√t * u)) := by
      ext u
      dsimp [G]
      have hid1 : 4 * (√t * u) ^ 4 - 12 * (√t * u) ^ 2 + 3 =
          4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3 := by
        calc 4 * (√t * u) ^ 4 - 12 * (√t * u) ^ 2 + 3
            = 4 * ((√t ^ 2) ^ 2 * u ^ 4) - 12 * (√t ^ 2 * u ^ 2) + 3 := by ring
          _ = 4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3 := by rw [hsq]; ring
      have hid2 : -(√t * u) ^ 2 = -u ^ 2 * t := by
        calc -(√t * u) ^ 2 = -(√t ^ 2 * u ^ 2) := by ring
          _ = -u ^ 2 * t := by rw [hsq]; ring
      rw [hid1, hid2]
      calc |4 * t ^ 2 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)|
          = |t ^ 2 * (4 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t))| := by
            congr 1; ring
        _ = |t ^ 2| * |4 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)| :=
            abs_mul _ _
        _ = t ^ 2 * |4 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)| := by
            rw [abs_of_nonneg (sq_nonneg t)]
    rw [hpt, intervalIntegral.integral_const_mul, hcomp, smul_eq_mul]
    have htsq : t ^ 2 * (√t)⁻¹ = t * √t := by
      calc t ^ 2 * (√t)⁻¹ = (√t ^ 2) ^ 2 * (√t)⁻¹ := by rw [hsq]
        _ = √t ^ 2 * √t := by field_simp
        _ = t * √t := by rw [hsq]
    rw [← mul_assoc, htsq]
  rw [heq]
  have hle := phi3_integral_bound (√t * a) (√t * b) (mul_le_mul_of_nonneg_left hab hsqrt.le)
  have hpos : 0 ≤ t * √t := by positivity
  nlinarith

private lemma P3_gauss_bounds (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) + 2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
      |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀| ≤
        (11 / 60) * (2 * δ) * t * √t := by
  intro h h'
  -- Define f and its derivatives for a single Gaussian exp (-u^2 * t)
  let f : ℝ → ℝ := fun u => Real.exp (-u ^ 2 * t)
  let f1 : ℝ → ℝ := fun u => -2 * t * u * Real.exp (-u ^ 2 * t)
  let f2 : ℝ → ℝ := fun u => 2 * t * (2 * u ^ 2 * t - 1) * Real.exp (-u ^ 2 * t)
  let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * u * (2 * u ^ 2 * t - 3) * Real.exp (-u ^ 2 * t)
  let f4 : ℝ → ℝ := fun u => 4 * t ^ 2 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)
  have hf1 : ∀ u, HasDerivAt f (f1 u) u := by
    intro u
    have harg : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * t * u) u :=
      (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
    exact (harg.exp).congr_deriv (by dsimp [f1]; ring)
  have hf2 : ∀ u, HasDerivAt f1 (f2 u) u := by
    intro u
    have hlin : HasDerivAt (fun x : ℝ => -2 * t * x) (-2 * t) u := by
      simpa using (hasDerivAt_id u).const_mul (-2 * t)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (f1 u) u := hf1 u
    exact (hlin.fun_mul hexp).congr_deriv (by dsimp [f1, f2]; ring)
  have hf3 : ∀ u, HasDerivAt f2 (f3 u) u := by
    intro u
    have hpoly : HasDerivAt (fun x : ℝ => 2 * t * (2 * x ^ 2 * t - 1)) (8 * t ^ 2 * u) u := by
      have hp := ((hasDerivAt_pow 2 u).const_mul (2 : ℝ)).mul_const t
      have hs := hp.fun_sub (hasDerivAt_const u (1 : ℝ))
      exact (hs.const_mul (2 * t)).congr_deriv (by ring)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (f1 u) u := hf1 u
    exact (hpoly.fun_mul hexp).congr_deriv (by dsimp [f1, f3]; ring)
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
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (f1 u) u := hf1 u
    exact (hpoly.fun_mul hexp).congr_deriv (by dsimp [f1, f4]; ring)
  -- Express h, h', h'', h''' using f, f1, f2, f3
  let h'' : ℝ → ℝ := fun w => f2 (w - δ) - f2 (w + δ)
  let h''' : ℝ → ℝ := fun w => f3 (w - δ) - f3 (w + δ)
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
    have heq_fn : h' = fun w => f1 (w - δ) - f1 (w + δ) := by
      ext x; dsimp [h', f1]; ring
    rw [heq_fn]
    exact h1.fun_sub h2
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
  have hc0 : Continuous h := continuous_iff_continuousAt.mpr fun w => (hh_deriv w).continuousAt
  have hc''' : Continuous h''' := by
    dsimp [h''', f3]; fun_prop
  -- Summability of h(a₀ + 1/2 + k)
  have hbd_f : ∀ c : ℝ, Summable (fun k : ℕ => Real.exp (-(a₀ + 1 / 2 + k + c) ^ 2 * t)) := by
    intro c
    obtain ⟨K, hK⟩ := exists_nat_gt (|a₀ + 1 / 2 + c| + 1)
    rw [← summable_nat_add_iff K]
    have hgeom : Summable (fun k : ℕ => (Real.exp (-t)) ^ k) :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
    refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hgeom
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have hk1 : (1 : ℝ) ≤ a₀ + 1 / 2 + (k + K : ℕ) + c := by
      have := neg_abs_le (a₀ + 1 / 2 + c)
      push_cast; linarith
    have hk2 : ((k : ℝ)) ≤ (a₀ + 1 / 2 + (k + K : ℕ) + c) ^ 2 := by
      have : (k : ℝ) ≤ (a₀ + 1 / 2 + (k + K : ℕ) + c) := by
        have := neg_abs_le (a₀ + 1 / 2 + c)
        push_cast; linarith
      nlinarith
    nlinarith
  have hsum_h : Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) :=
    (hbd_f (-δ)).sub (hbd_f δ)
  refine ⟨hsum_h, ?_⟩
  -- For every N, telescope P3_cell_identity over k = 0..N-1
  let I_f4 : ℝ := (113 / 5) * t * √t
  have hfinite : ∀ N : ℕ, 1 ≤ N →
      |(∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k)) -
        (∫ w in a₀..(a₀ + N), h w) -
        (1 / 24) * (h' a₀ - h' (a₀ + N))| ≤
      (1 / 124) * (2 * δ) * I_f4 := by
    intro N hN
    let rem : ℕ → ℝ := fun k =>
      (∫ r in (-1 / 2 : ℝ)..0, P3 r * h''' (a₀ + 1 / 2 + k + r)) +
        (∫ r in (0 : ℝ)..(1 / 2), P3 r * h''' (a₀ + 1 / 2 + k + r))
    have hsum_id : (∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k)) - (∫ w in a₀..(a₀ + N), h w) =
        (1 / 24) * (h' a₀ - h' (a₀ + N)) - ∑ k ∈ Finset.range N, rem k := by
      have hidk : ∀ k : ℕ, h (a₀ + 1 / 2 + k) -
          (∫ w in (a₀ + k : ℝ)..(a₀ + (k + 1 : ℕ)), h w) =
          (1 / 24) * (h' (a₀ + k) - h' (a₀ + (k + 1 : ℕ))) - rem k := by
        intro k
        have hcell := P3_cell_identity h h' h'' h''' (a₀ + 1 / 2 + k) hh_deriv hh'_deriv hh''_deriv hc'''
        have ha1 : a₀ + 1 / 2 + k - 1 / 2 = a₀ + k := by ring
        have ha2 : a₀ + 1 / 2 + k + 1 / 2 = a₀ + (k + 1 : ℕ) := by push_cast; ring
        rw [ha1, ha2] at hcell
        exact hcell
      have hsum_cell : ∑ k ∈ Finset.range N,
          (h (a₀ + 1 / 2 + k) - ∫ w in (a₀ + k : ℝ)..(a₀ + (k + 1 : ℕ)), h w) =
          ∑ k ∈ Finset.range N, ((1 / 24) * (h' (a₀ + k) - h' (a₀ + (k + 1 : ℕ))) - rem k) :=
        Finset.sum_congr rfl fun k _ => hidk k
      conv_lhs at hsum_cell => rw [Finset.sum_sub_distrib]
      conv_rhs at hsum_cell => rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
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
        have := Finset.sum_range_sub' (fun k : ℕ => h' (a₀ + k)) N
        simpa using this
      rw [hteles_int, hteles_h'] at hsum_cell
      exact hsum_cell
    have hdiff_eq : (∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k)) -
        (∫ w in a₀..(a₀ + N), h w) - (1 / 24) * (h' a₀ - h' (a₀ + N)) =
        -(∑ k ∈ Finset.range N, rem k) := by linarith
    rw [hdiff_eq, abs_neg]
    -- Bound |∑ rem k| via FTC h'''(w) = -∫_{w-δ}^{w+δ} f4(u) du
    have hh'''_eq : ∀ w, |h''' w| ≤ ∫ v in (-δ)..δ, |f4 (w + v)| := by
      intro w
      have hftc : f3 (w + δ) - f3 (w - δ) = ∫ u in (w - δ)..(w + δ), f4 u :=
        (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hf4 u)
          (Continuous.intervalIntegrable (by dsimp [f4]; fun_prop) _ _)).symm
      have hshift : ∫ u in (w - δ)..(w + δ), f4 u = ∫ v in (-δ)..δ, f4 (w + v) := by
        have := intervalIntegral.integral_comp_add_left f4 w (a := -δ) (b := δ)
        convert this.symm using 2; ring
      have hneg : h''' w = -(∫ v in (-δ)..δ, f4 (w + v)) := by
        dsimp [h''']; rw [← hshift, ← hftc]; ring
      rw [hneg, abs_neg]
      exact intervalIntegral.abs_integral_le_integral_abs (by linarith)
    have hrem_le : ∀ k : ℕ, |rem k| ≤
        (1 / 124) * ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)| := by
      intro k
      have hcont_inner : Continuous (fun r : ℝ => ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)|) := by
        have hcont2 : Continuous (fun p : ℝ × ℝ => |f4 (a₀ + 1 / 2 + k + p.1 + p.2)|) := by
          dsimp [f4]; fun_prop
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont2 (-δ) δ
      have hhalf_le : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) → b ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) →
          |∫ r in a..b, P3 r * h''' (a₀ + 1 / 2 + k + r)| ≤
            (1 / 124) * ∫ r in a..b, ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)| := by
        intro a b hab ha hb
        refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
        have hi1 : IntervalIntegrable (fun r => |P3 r * h''' (a₀ + 1 / 2 + k + r)|) volume a b :=
          ((continuous_P3.mul (hc'''.comp (continuous_const.add continuous_id))).abs).intervalIntegrable a b
        have hi2 : IntervalIntegrable (fun r => (1 / 124 : ℝ) * ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)|) volume a b :=
          (continuous_const.mul hcont_inner).intervalIntegrable a b
        have hmono := intervalIntegral.integral_mono_on hab hi1 hi2 fun r hr => ?_
        · rw [intervalIntegral.integral_const_mul] at hmono
          exact hmono
        · rw [abs_mul]
          have hr1 : -1 / 2 ≤ r := le_trans ha.1 hr.1
          have hr2 : r ≤ 1 / 2 := le_trans hr.2 hb.2
          exact mul_le_mul (abs_P3_le hr1 hr2) (hh'''_eq (a₀ + 1 / 2 + k + r)) (abs_nonneg _) (by positivity)
      have hL := hhalf_le (-1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
      have hR := hhalf_le 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      have hsplit : ∫ r in (-1 / 2 : ℝ)..(1 / 2), (∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)|) =
          (∫ r in (-1 / 2 : ℝ)..0, ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)|) +
            (∫ r in (0 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)|) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_inner.intervalIntegrable _ _) (hcont_inner.intervalIntegrable _ _)).symm
      dsimp [rem]
      have htri := abs_add_le
        (∫ r in (-1 / 2 : ℝ)..0, P3 r * h''' (a₀ + 1 / 2 + k + r))
        (∫ r in (0 : ℝ)..(1 / 2), P3 r * h''' (a₀ + 1 / 2 + k + r))
      linarith
    -- Swap r and v integrals and telescope over k
    have hsum_rem : |∑ k ∈ Finset.range N, rem k| ≤ (1 / 124) * (2 * δ) * I_f4 := by
      have h1 : |∑ k ∈ Finset.range N, rem k| ≤ ∑ k ∈ Finset.range N, |rem k| := Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ k ∈ Finset.range N, |rem k| ≤
          (1 / 124) * ∑ k ∈ Finset.range N,
            ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)| := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => hrem_le k
      have hswap_k : ∀ k : ℕ,
          (∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)|) =
            ∫ v in (-δ)..δ, ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u| := by
        intro k
        have hcont2 : Continuous (fun p : ℝ × ℝ => |f4 (a₀ + 1 / 2 + k + p.1 + p.2)|) := by
          dsimp [f4]; fun_prop
        have hint_prod : Integrable (fun p : ℝ × ℝ => |f4 (a₀ + 1 / 2 + k + p.1 + p.2)|)
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
        have hcomp := intervalIntegral.integral_comp_add_left (fun u => |f4 u|)
          (a₀ + 1 / 2 + k + v) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        have hpt : (fun r => |f4 (a₀ + 1 / 2 + k + r + v)|) =
            (fun r => |f4 (a₀ + 1 / 2 + k + v + r)|) := by
          ext r; ring_nf
        rw [hpt]
        convert hcomp using 2 <;> push_cast <;> ring
      have hc_v : ∀ k : ℕ, Continuous (fun v : ℝ =>
          ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u|) := by
        intro k
        have hsub : ∀ v, ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u| =
            ∫ w in (0 : ℝ)..1, |f4 (a₀ + k + v + w)| := by
          intro v
          have hcomp := intervalIntegral.integral_comp_add_left (fun u => |f4 u|) (a₀ + k + v)
            (a := (0 : ℝ)) (b := (1 : ℝ))
          have hb_eq : a₀ + (k + 1 : ℕ) + v = a₀ + k + v + 1 := by push_cast; ring
          rw [add_zero, ← hb_eq] at hcomp
          exact hcomp.symm
        simp_rw [hsub]
        have hcont_vw : Continuous (fun p : ℝ × ℝ => |f4 (a₀ + k + p.1 + p.2)|) := by
          dsimp [f4]; fun_prop
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont_vw 0 1
      have hsum_swap : ∑ k ∈ Finset.range N,
          ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)| =
          ∫ v in (-δ)..δ, ∑ k ∈ Finset.range N,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u| := by
        simp_rw [hswap_k]
        rw [← intervalIntegral.integral_finsetSum]
        intro k _
        exact (hc_v k).intervalIntegrable (-δ) δ
      have htele_f4 : ∀ v, ∑ k ∈ Finset.range N,
          ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u| ≤ I_f4 := by
        intro v
        have hsum_eq : ∀ M : ℕ, ∑ k ∈ Finset.range M,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u| =
            ∫ u in (a₀ + v)..(a₀ + M + v), |f4 u| := by
          intro M
          induction M with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ, ih]
            have hc_abs : Continuous (fun u => |f4 u|) := by dsimp [f4]; fun_prop
            exact intervalIntegral.integral_add_adjacent_intervals
              (hc_abs.intervalIntegrable _ _) (hc_abs.intervalIntegrable _ _)
        rw [hsum_eq N]
        exact f_fourth_integral_bound (a₀ + v) (a₀ + N + v) t ht (by linarith)
      have hint_ub : ∫ v in (-δ)..δ, ∑ k ∈ Finset.range N,
          ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u| ≤ (2 * δ) * I_f4 := by
        have hc_sum : IntervalIntegrable (fun v => ∑ k ∈ Finset.range N,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u|) volume (-δ) δ :=
          (continuous_finsetSum _ fun k _ => hc_v k).intervalIntegrable (-δ) δ
        have hm := intervalIntegral.integral_mono_on (by linarith : -δ ≤ δ) hc_sum
          intervalIntegrable_const (fun v _ => htele_f4 v)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
        linarith
      calc |∑ k ∈ Finset.range N, rem k|
          ≤ ∑ k ∈ Finset.range N, |rem k| := h1
        _ ≤ (1 / 124) * ∑ k ∈ Finset.range N,
            ∫ r in (-1 / 2 : ℝ)..(1 / 2), ∫ v in (-δ)..δ, |f4 (a₀ + 1 / 2 + k + r + v)| := h2
        _ = (1 / 124) * ∫ v in (-δ)..δ, ∑ k ∈ Finset.range N,
            ∫ u in (a₀ + k + v)..(a₀ + (k + 1 : ℕ) + v), |f4 u| := by rw [hsum_swap]
        _ ≤ (1 / 124) * ((2 * δ) * I_f4) := mul_le_mul_of_nonneg_left hint_ub (by norm_num)
        _ = (1 / 124) * (2 * δ) * I_f4 := by ring
    exact hsum_rem
  -- Take N → ∞ in hfinite
  have htend_sum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, h (a₀ + 1 / 2 + k))
      atTop (𝓝 (∑' k : ℕ, h (a₀ + 1 / 2 + k))) :=
    hsum_h.hasSum.tendsto_sum_nat
  have htend_h' : Tendsto (fun N : ℕ => h' (a₀ + N)) atTop (𝓝 0) := by
    have htend_term : ∀ c : ℝ, Tendsto (fun N : ℕ => (a₀ + N + c) * Real.exp (-(a₀ + N + c) ^ 2 * t))
        atTop (𝓝 0) := by
      intro c
      have harg : Tendsto (fun N : ℕ => a₀ + (N : ℝ) + c) atTop atTop :=
        (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds
      have h0 : Tendsto (fun u : ℝ => u * Real.exp (-t * u ^ 2)) atTop (𝓝 0) := by
        have hb : ∀ᶠ u : ℝ in atTop, u * Real.exp (-t * u ^ 2) ∈ Set.Icc 0 ((1 / t) * u⁻¹) := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
          refine ⟨mul_nonneg hu.le (Real.exp_pos _).le, ?_⟩
          have hexp_lb : t * u ^ 2 ≤ Real.exp (t * u ^ 2) := by
            linarith [Real.add_one_le_exp (t * u ^ 2)]
          have htu : 0 < t * u ^ 2 := by positivity
          have hinv : Real.exp (-t * u ^ 2) ≤ (t * u ^ 2)⁻¹ := by
            rw [show -t * u ^ 2 = -(t * u ^ 2) by ring, Real.exp_neg]
            exact inv_anti₀ htu hexp_lb
          calc u * Real.exp (-t * u ^ 2)
              ≤ u * (t * u ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hu.le
            _ = (1 / t) * u⁻¹ := by field_simp
        have htend_inv : Tendsto (fun u : ℝ => (1 / t) * u⁻¹) atTop (𝓝 0) := by
          have hzero : (1 / t : ℝ) * 0 = 0 := mul_zero _
          rw [← hzero]
          exact tendsto_inv_atTop_zero.const_mul (1 / t)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend_inv
          (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
      refine (h0.comp harg).congr fun N => ?_
      dsimp; ring_nf
    have h1 := ((htend_term (-δ)).const_mul (-2 * t)).add ((htend_term δ).const_mul (2 * t))
    simpa [mul_zero, add_zero] using h1.congr fun N => by dsimp [h']; ring
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
        simp [intervalIntegral.integral_comp_add_right f δ]
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
      rw [hsub, hid1, hid2]
      ring
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
        (1 / 24) * (h' a₀ - h' (a₀ + N))|) atTop
      (𝓝 |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀|) := by
    simpa only [sub_zero] using ((htend_sum.sub htend_int).sub
      (((tendsto_const_nhds (x := h' a₀)).sub htend_h').const_mul (1 / 24 : ℝ))).abs
  have hle_lim : |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
      (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀| ≤
      (1 / 124) * (2 * δ) * I_f4 :=
    le_of_tendsto htend_lhs (by filter_upwards [eventually_ge_atTop 1] with N hN; exact hfinite N hN)
  have hconst : (1 / 124 : ℝ) * (2 * δ) * I_f4 ≤ (11 / 60) * (2 * δ) * t * √t := by
    dsimp [I_f4]
    have hpos : 0 ≤ (2 * δ) * t * √t := by positivity
    nlinarith
  exact le_trans hle_lim hconst


lemma p3_aux (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) + 2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
      |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀| ≤
        (11 / 60) * (2 * δ) * t * √t := P3_gauss_bounds a₀ δ t hδ ht

end SolGammaHelpers

theorem solution (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) + 2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
      |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀| ≤
        (11 / 60) * (2 * δ) * t * √t :=
  SolGammaHelpers.p3_aux a₀ δ t hδ ht
