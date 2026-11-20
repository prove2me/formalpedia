-- Prove2me | solution 1 for RademacherGamma_gaussian_sum_ge_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:05:55.866742+00:00
-- url     : https://prove2.me/submissions/61c1d585-2c58-4fd3-9933-66d3cf07290d

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_RademacherGamma_p3_gauss_bounds
import Theorems.Thm_RademacherGamma_p5_gauss_bounds
import Theorems.Thm_RademacherGamma_gaussian_sum_ge_c1_box

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
private lemma P5_gauss_bounds (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) +
        2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * u * (2 * u ^ 2 * t - 3) * Real.exp (-u ^ 2 * t)
    let h''' : ℝ → ℝ := fun w => f3 (w - δ) - f3 (w + δ)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
    |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) - (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) -
      (1 / 24) * h' a₀ + (7 / 5760) * h''' a₀| ≤ (1 / 24) * (2 * δ) * t ^ 2 * √t :=
  RademacherGamma_p5_gauss_bounds a₀ δ t hδ ht

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


private lemma exp_neg_le_poly4 {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - Real.exp (-t))
      (-1 + y - y ^ 2 / 2 + y ^ 3 / 6 + Real.exp (-y)) y := by
    intro y
    have hpoly : HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24)
        (-1 + y - y ^ 2 / 2 + y ^ 3 / 6) y := by
      have h1 : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) y := by
        simpa using (hasDerivAt_const y (1 : ℝ)).fun_sub (hasDerivAt_id y)
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y :=
        ((hasDerivAt_pow 2 y).div_const 2).congr_deriv (by ring)
      have h3 : HasDerivAt (fun t : ℝ => t ^ 3 / 6) (y ^ 2 / 2) y :=
        ((hasDerivAt_pow 3 y).div_const 6).congr_deriv (by ring)
      have h4 : HasDerivAt (fun t : ℝ => t ^ 4 / 24) (y ^ 3 / 6) y :=
        ((hasDerivAt_pow 4 y).div_const 24).congr_deriv (by ring)
      exact (((h1.fun_add h2).fun_sub h3).fun_add h4).congr_deriv (by ring)
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-y)) y := by
      simpa using (hasDerivAt_id y).neg.exp
    exact (hpoly.fun_sub hexp).congr_deriv (by ring)
  have hmono : (fun t : ℝ => 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - Real.exp (-t)) 0 ≤
      (fun t : ℝ => 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - Real.exp (-t)) x :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy
        rw [(hderiv y).deriv]
        have := exp_neg_ge_poly3 hy.le
        linarith)
      (by simp) hx hx
  simp at hmono
  linarith

private lemma exp_neg_ge_poly5 {x : ℝ} (hx : 0 ≤ x) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 ≤ Real.exp (-x) := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120))
      (-Real.exp (-y) + (1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24)) y := by
    intro y
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-y)) y := by
      simpa using (hasDerivAt_id y).neg.exp
    have hpoly : HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120)
        (-1 + y - y ^ 2 / 2 + y ^ 3 / 6 - y ^ 4 / 24) y := by
      have h1 : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) y := by
        simpa using (hasDerivAt_const y (1 : ℝ)).fun_sub (hasDerivAt_id y)
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y :=
        ((hasDerivAt_pow 2 y).div_const 2).congr_deriv (by ring)
      have h3 : HasDerivAt (fun t : ℝ => t ^ 3 / 6) (y ^ 2 / 2) y :=
        ((hasDerivAt_pow 3 y).div_const 6).congr_deriv (by ring)
      have h4 : HasDerivAt (fun t : ℝ => t ^ 4 / 24) (y ^ 3 / 6) y :=
        ((hasDerivAt_pow 4 y).div_const 24).congr_deriv (by ring)
      have h5 : HasDerivAt (fun t : ℝ => t ^ 5 / 120) (y ^ 4 / 24) y :=
        ((hasDerivAt_pow 5 y).div_const 120).congr_deriv (by ring)
      exact ((((h1.fun_add h2).fun_sub h3).fun_add h4).fun_sub h5).congr_deriv (by ring)
    exact (hexp.fun_sub hpoly).congr_deriv (by ring)
  have hmono : (fun t : ℝ => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120)) 0 ≤
      (fun t : ℝ => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120)) x :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy
        rw [(hderiv y).deriv]
        have := exp_neg_le_poly4 hy.le
        linarith)
      (by simp) hx hx
  simp at hmono
  linarith

private lemma one_sub_exp_neg_div_antitone :
    AntitoneOn (fun u : ℝ => (1 - Real.exp (-u)) / u) (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact ContinuousOn.div (by fun_prop) continuous_id.continuousOn fun u hu => ne_of_gt hu
  · intro u hu
    rw [interior_Ioi, Set.mem_Ioi] at hu
    have hnum : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-u)) u := by
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-u)) u := by
        simpa using (hasDerivAt_id u).neg.exp
      simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub hexp
    have hid : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id u
    exact (hnum.fun_div hid (ne_of_gt hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    rw [Set.mem_Ioi] at hu
    have hnum : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-u)) u := by
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-u)) u := by
        simpa using (hasDerivAt_id u).neg.exp
      simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub hexp
    have hid : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id u
    have hder := hnum.fun_div hid (ne_of_gt hu)
    rw [hder.deriv]
    have hle : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hmul : (1 + u) * Real.exp (-u) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos u)]
      exact hle
    have hnum_nonpos : Real.exp (-u) * u - (1 - Real.exp (-u)) * 1 ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (sq_nonneg u)

private lemma one_sub_exp_neg_div_le_poly4 {u : ℝ} (hu : 0 < u) :
    (1 - Real.exp (-u)) / u ≤ 1 - u / 2 + u ^ 2 / 6 - u ^ 3 / 24 + u ^ 4 / 120 := by
  have h5 := exp_neg_ge_poly5 hu.le
  rw [div_le_iff₀ hu]
  have hid : (1 - u / 2 + u ^ 2 / 6 - u ^ 3 / 24 + u ^ 4 / 120) * u =
      u - u ^ 2 / 2 + u ^ 3 / 6 - u ^ 4 / 24 + u ^ 5 / 120 := by ring
  linarith

private lemma cosh_le_poly4 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 5) :
    (Real.exp x + Real.exp (-x)) / 2 ≤ 1 + x ^ 2 / 2 + x ^ 4 / 20 := by
  let g : ℝ → ℝ := fun t => 1 + t ^ 2 / 2 + t ^ 4 / 20 - (Real.exp t + Real.exp (-t)) / 2
  let g1 : ℝ → ℝ := fun t => t + t ^ 3 / 5 - (Real.exp t - Real.exp (-t)) / 2
  let g2 : ℝ → ℝ := fun t => 1 + 3 * t ^ 2 / 5 - (Real.exp t + Real.exp (-t)) / 2
  let g3 : ℝ → ℝ := fun t => 6 * t / 5 - (Real.exp t - Real.exp (-t)) / 2
  have hg_der : ∀ t, HasDerivAt g (g1 t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => 1 + u ^ 2 / 2 + u ^ 4 / 20) (t + t ^ 3 / 5) t := by
      have ha : HasDerivAt (fun u : ℝ => (1 : ℝ) + u ^ 2 / 2) t t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).fun_add
          (((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring))
      have hb : HasDerivAt (fun u : ℝ => u ^ 4 / 20) (t ^ 3 / 5) t :=
        ((hasDerivAt_pow 4 t).div_const 20).congr_deriv (by ring)
      exact ha.fun_add hb
    have h2 : HasDerivAt (fun u : ℝ => (Real.exp u + Real.exp (-u)) / 2)
        ((Real.exp t - Real.exp (-t)) / 2) t := by
      have hexp2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_id t).neg.exp
      exact (((Real.hasDerivAt_exp t).fun_add hexp2).div_const 2).congr_deriv (by ring)
    exact (h1.fun_sub h2).congr_deriv (by dsimp [g1])
  have hg1_der : ∀ t, HasDerivAt g1 (g2 t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => u + u ^ 3 / 5) (1 + 3 * t ^ 2 / 5) t := by
      exact ((hasDerivAt_id t).fun_add ((hasDerivAt_pow 3 t).div_const 5)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u : ℝ => (Real.exp u - Real.exp (-u)) / 2)
        ((Real.exp t + Real.exp (-t)) / 2) t := by
      have hexp2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_id t).neg.exp
      exact (((Real.hasDerivAt_exp t).fun_sub hexp2).div_const 2).congr_deriv (by ring)
    exact (h1.fun_sub h2).congr_deriv (by dsimp [g2])
  have hg2_der : ∀ t, HasDerivAt g2 (g3 t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => 1 + 3 * u ^ 2 / 5) (6 * t / 5) t := by
      have ha : HasDerivAt (fun u : ℝ => 3 * u ^ 2 / 5) (6 * t / 5) t :=
        (((hasDerivAt_pow 2 t).const_mul (3 : ℝ)).div_const 5).congr_deriv (by ring)
      exact (hasDerivAt_const t (1 : ℝ)).fun_add ha |>.congr_deriv (by ring)
    have h2 : HasDerivAt (fun u : ℝ => (Real.exp u + Real.exp (-u)) / 2)
        ((Real.exp t - Real.exp (-t)) / 2) t := by
      have hexp2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_id t).neg.exp
      exact (((Real.hasDerivAt_exp t).fun_add hexp2).div_const 2).congr_deriv (by ring)
    exact (h1.fun_sub h2).congr_deriv (by dsimp [g3])
  have hg3_der : ∀ t, HasDerivAt g3 (6 / 5 - (Real.exp t + Real.exp (-t)) / 2) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => 6 * u / 5) (6 / 5) t :=
      (((hasDerivAt_id t).const_mul (6 : ℝ)).div_const 5).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u : ℝ => (Real.exp u - Real.exp (-u)) / 2)
        ((Real.exp t + Real.exp (-t)) / 2) t := by
      have hexp2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_id t).neg.exp
      exact (((Real.hasDerivAt_exp t).fun_sub hexp2).div_const 2).congr_deriv (by ring)
    exact (h1.fun_sub h2).congr_deriv (by ring)
  have hcosh_mono : MonotoneOn (fun t : ℝ => Real.exp t + Real.exp (-t)) (Set.Icc 0 (3 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (by fun_prop : Continuous (fun t : ℝ => Real.exp t + Real.exp (-t))).continuousOn
    · intro t _
      have hexp2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_id t).neg.exp
      exact ((Real.hasDerivAt_exp t).fun_add hexp2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hexp2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_id t).neg.exp
      rw [((Real.hasDerivAt_exp t).fun_add hexp2).deriv]
      have hle : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith only [ht.1])
      linarith
  have hcosh_35 : (Real.exp (3 / 5 : ℝ) + Real.exp (-(3 / 5 : ℝ))) / 2 ≤ 6 / 5 := by
    have hpos_e : Real.exp (3 / 5 : ℝ) ≤ 1 / (1 - (3 / 5 : ℝ) + (3 / 5 : ℝ) ^ 2 / 2 - (3 / 5 : ℝ) ^ 3 / 6) := by
      have hneg := exp_neg_ge_poly3 (show (0 : ℝ) ≤ 3 / 5 by norm_num)
      have hp : (0 : ℝ) < 1 - 3 / 5 + (3 / 5 : ℝ) ^ 2 / 2 - (3 / 5 : ℝ) ^ 3 / 6 := by norm_num
      have hrw : Real.exp (3 / 5 : ℝ) = (Real.exp (-(3 / 5 : ℝ)))⁻¹ := by rw [Real.exp_neg, inv_inv]
      rw [hrw, one_div]
      exact inv_anti₀ hp hneg
    have hneg_e : Real.exp (-(3 / 5 : ℝ)) ≤
        1 / (1 + (3 / 5 : ℝ) + (3 / 5 : ℝ) ^ 2 / 2 + (3 / 5 : ℝ) ^ 3 / 6) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (exp_ge_poly3 (by norm_num))
    nlinarith only [hpos_e, hneg_e]
  have hg3_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) (3 / 5), 0 ≤ g3 t := by
    intro t ht
    have hmono : MonotoneOn g3 (Set.Icc 0 (3 / 5)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact (by dsimp [g3]; fun_prop : Continuous g3).continuousOn
      · exact fun u _ => (hg3_der u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hg3_der u).deriv]
        have hm := hcosh_mono ⟨hu.1.le, hu.2.le⟩ ⟨by norm_num, le_rfl⟩ hu.2.le
        linarith only [hm, hcosh_35]
    have h0 : g3 0 = 0 := by dsimp [g3]; norm_num
    linarith [hmono ⟨le_rfl, by norm_num⟩ ht ht.1, h0]
  have hg2_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) (3 / 5), 0 ≤ g2 t := by
    intro t ht
    have hmono : MonotoneOn g2 (Set.Icc 0 (3 / 5)) :=
      monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (by dsimp [g2]; fun_prop : Continuous g2).continuousOn
        (fun u _ => (hg2_der u).differentiableAt.differentiableWithinAt)
        fun u hu => by rw [interior_Icc] at hu; rw [(hg2_der u).deriv]; exact hg3_nonneg u ⟨hu.1.le, hu.2.le⟩
    have h0 : g2 0 = 0 := by dsimp [g2]; norm_num
    linarith [hmono ⟨le_rfl, by norm_num⟩ ht ht.1, h0]
  have hg1_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) (3 / 5), 0 ≤ g1 t := by
    intro t ht
    have hmono : MonotoneOn g1 (Set.Icc 0 (3 / 5)) :=
      monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (by dsimp [g1]; fun_prop : Continuous g1).continuousOn
        (fun u _ => (hg1_der u).differentiableAt.differentiableWithinAt)
        fun u hu => by rw [interior_Icc] at hu; rw [(hg1_der u).deriv]; exact hg2_nonneg u ⟨hu.1.le, hu.2.le⟩
    have h0 : g1 0 = 0 := by dsimp [g1]; norm_num
    linarith [hmono ⟨le_rfl, by norm_num⟩ ht ht.1, h0]
  have hg_mono : MonotoneOn g (Set.Icc 0 (3 / 5)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (by dsimp [g]; fun_prop : Continuous g).continuousOn
      (fun u _ => (hg_der u).differentiableAt.differentiableWithinAt)
      fun u hu => by rw [interior_Icc] at hu; rw [(hg_der u).deriv]; exact hg1_nonneg u ⟨hu.1.le, hu.2.le⟩
  have h0 : g 0 = 0 := by dsimp [g]; norm_num
  have hgx := hg_mono ⟨le_rfl, by norm_num⟩ ⟨hx0, hx1⟩ hx0
  dsimp [g] at hgx
  norm_num at hgx
  linarith


private lemma h_gauss_nonneg {w δ t : ℝ} (hw : δ ≤ w) (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    0 ≤ Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t) := by
  have hsq : (w - δ) ^ 2 ≤ (w + δ) ^ 2 := by nlinarith only [hw, hδ]
  have hexp : Real.exp (-(w + δ) ^ 2 * t) ≤ Real.exp (-(w - δ) ^ 2 * t) :=
    Real.exp_le_exp.mpr (by nlinarith only [hsq, ht])
  linarith

private lemma case2_tsum_reindex (y η t : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 2) (ht : 0 < t) :
    let δ := 1 / 2 - η
    let h := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let htilde := fun w => Real.exp (-(w - η) ^ 2 * t) - Real.exp (-(w + η) ^ 2 * t)
    Summable (fun k : ℕ => h (y + k)) ∧
    Summable (fun m : ℕ => htilde (y + 1 / 2 + m)) ∧
    ∑' k : ℕ, h (y + k) = Real.exp (-(y - 1 / 2 + η) ^ 2 * t) - ∑' m : ℕ, htilde (y + 1 / 2 + m) := by
  intro δ h htilde
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hs1 : Summable (fun k : ℕ => h (y + k)) := by
    have hpb := (P5_gauss_bounds (y - 1 / 2) δ t hδ ht).1
    refine hpb.congr fun k => ?_
    dsimp [h]; ring_nf
  have hs2 : Summable (fun m : ℕ => htilde (y + 1 / 2 + m)) :=
    (P5_gauss_bounds y η t hη0 ht).1
  have hsum_eq : ∀ N : ℕ,
      ∑ k ∈ Finset.range (N + 1), h (y + k) =
        Real.exp (-(y - 1 / 2 + η) ^ 2 * t) -
          (∑ m ∈ Finset.range N, htilde (y + 1 / 2 + m)) -
          Real.exp (-(y + 1 / 2 + N - η) ^ 2 * t) := by
    intro N
    induction N with
    | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero,
        Finset.range_zero, Finset.sum_empty, sub_zero]
      dsimp [h, δ]; ring_nf
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hterm : h (y + ((N + 1 : ℕ) : ℝ)) =
          Real.exp (-(y + 1 / 2 + N + η) ^ 2 * t) -
          Real.exp (-(y + 1 / 2 + ((N + 1 : ℕ) : ℝ) - η) ^ 2 * t) := by
        dsimp [h, δ]; push_cast; ring_nf
      have htilde_N : htilde (y + 1 / 2 + N) =
          Real.exp (-(y + 1 / 2 + N - η) ^ 2 * t) -
          Real.exp (-(y + 1 / 2 + N + η) ^ 2 * t) := by
        dsimp [htilde]
      rw [hterm, htilde_N]
      ring
  have htend1 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), h (y + k)) atTop
      (𝓝 (∑' k : ℕ, h (y + k))) :=
    hs1.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have htend2 : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, htilde (y + 1 / 2 + m)) atTop
      (𝓝 (∑' m : ℕ, htilde (y + 1 / 2 + m))) :=
    hs2.hasSum.tendsto_sum_nat
  have htend3 : Tendsto (fun N : ℕ => Real.exp (-(y + 1 / 2 + N - η) ^ 2 * t)) atTop (𝓝 0) := by
    refine tendsto_exp_atBot.comp ?_
    have hnat : Tendsto (fun N : ℕ => y + 1 / 2 + (N : ℝ) - η) atTop atTop :=
      (tendsto_atTop_add_const_left atTop (y + 1 / 2 - η) tendsto_natCast_atTop_atTop).congr
        fun N => by ring
    exact (tendsto_neg_atTop_atBot.comp
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_mul_const ht)).comp hnat |>.congr fun N => by
      dsimp [Function.comp_def]; ring
  have htend_rhs : Tendsto (fun N : ℕ =>
      Real.exp (-(y - 1 / 2 + η) ^ 2 * t) -
        (∑ m ∈ Finset.range N, htilde (y + 1 / 2 + m)) -
        Real.exp (-(y + 1 / 2 + N - η) ^ 2 * t)) atTop
      (𝓝 (Real.exp (-(y - 1 / 2 + η) ^ 2 * t) - ∑' m : ℕ, htilde (y + 1 / 2 + m))) := by
    simpa only [sub_zero] using ((tendsto_const_nhds).sub htend2).sub htend3
  have htend_lhs : Tendsto (fun N : ℕ =>
      Real.exp (-(y - 1 / 2 + η) ^ 2 * t) -
        (∑ m ∈ Finset.range N, htilde (y + 1 / 2 + m)) -
        Real.exp (-(y + 1 / 2 + N - η) ^ 2 * t)) atTop
      (𝓝 (∑' k : ℕ, h (y + k))) :=
    htend1.congr fun N => (hsum_eq N)
  exact ⟨hs1, hs2, tendsto_nhds_unique htend_lhs htend_rhs⟩

private lemma h_gauss_antitone_tail {a₀ δ t : ℝ} (haδ : 0 ≤ a₀ - δ) (hδ : 0 < δ) (ht : 0 < t)
    (hcond : 1 ≤ 2 * (a₀ - δ) ^ 2 * t) :
    AntitoneOn (fun w : ℝ => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t))
      (Set.Ici a₀) := by
  let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
  let g : ℝ → ℝ := fun u => u * Real.exp (-u ^ 2 * t)
  have hg_ant : AntitoneOn g (Set.Ici (a₀ - δ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact (by dsimp [g]; fun_prop : Continuous g).continuousOn
    · intro u _
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (-2 * u * t * Real.exp (-u ^ 2 * t)) u := by
        have hp : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
          (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
        convert hp.exp using 1; ring
      exact ((hasDerivAt_id u).fun_mul hexp).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici, Set.mem_Ioi] at hu
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (-2 * u * t * Real.exp (-u ^ 2 * t)) u := by
        have hp : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
          (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
        convert hp.exp using 1; ring
      have hid : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
      have hder := (hid.fun_mul hexp).congr_deriv (by
        show 1 * Real.exp (-u ^ 2 * t) + u * (-2 * u * t * Real.exp (-u ^ 2 * t)) =
          (1 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t); ring)
      rw [hder.deriv]
      have hu2 : (a₀ - δ) ^ 2 ≤ u ^ 2 := by nlinarith only [haδ, hu]
      have hle : 1 ≤ 2 * u ^ 2 * t := by nlinarith only [hu2, hcond, ht]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
  apply antitoneOn_of_deriv_nonpos (convex_Ici a₀)
  · exact (by dsimp [h]; fun_prop : Continuous h).continuousOn
  · intro w _
    have hid : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(x - δ) ^ 2 * t))
        (-2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t)) w := by
      have hp : HasDerivAt (fun x : ℝ => -(x - δ) ^ 2 * t) (-2 * (w - δ) * t) w :=
        ((((hid.sub_const δ).pow 2).neg).mul_const t).congr_deriv (by ring)
      convert hp.exp using 1; ring
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(x + δ) ^ 2 * t))
        (-2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)) w := by
      have hp : HasDerivAt (fun x : ℝ => -(x + δ) ^ 2 * t) (-2 * (w + δ) * t) w :=
        ((((hid.add_const δ).pow 2).neg).mul_const t).congr_deriv (by ring)
      convert hp.exp using 1; ring
    exact (h1.fun_sub h2).differentiableAt.differentiableWithinAt
  · intro w hw
    rw [interior_Ici, Set.mem_Ioi] at hw
    have hid : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(x - δ) ^ 2 * t))
        (-2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t)) w := by
      have hp : HasDerivAt (fun x : ℝ => -(x - δ) ^ 2 * t) (-2 * (w - δ) * t) w :=
        ((((hid.sub_const δ).pow 2).neg).mul_const t).congr_deriv (by ring)
      convert hp.exp using 1; ring
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(x + δ) ^ 2 * t))
        (-2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)) w := by
      have hp : HasDerivAt (fun x : ℝ => -(x + δ) ^ 2 * t) (-2 * (w + δ) * t) w :=
        ((((hid.add_const δ).pow 2).neg).mul_const t).congr_deriv (by ring)
      convert hp.exp using 1; ring
    have hder := (h1.fun_sub h2).congr_deriv (by
      show (-2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t)) -
        (-2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)) = -2 * t * (g (w - δ) - g (w + δ))
      dsimp [g]; ring)
    rw [hder.deriv]
    have hcmp := hg_ant (a := w - δ) (b := w + δ) (by simp only [Set.mem_Ici]; linarith)
      (by simp only [Set.mem_Ici]; linarith) (by linarith)
    nlinarith only [ht, hcmp]

private lemma gaussian_antitone_sum_ge_integral {y δ t : ℝ} (hyδ : 0 ≤ y - δ) (hδ : 0 < δ)
    (ht : 0 < t) (hcond : 1 ≤ 2 * (y - δ) ^ 2 * t)
    (hs : Summable (fun k : ℕ => Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t))) :
    ∫ v in (y - δ)..(y + δ), Real.exp (-v ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
  have hant := h_gauss_antitone_tail hyδ hδ ht hcond
  have hcont_h : Continuous h := by dsimp [h]; fun_prop
  have hstep : ∀ N : ℕ, ∫ w in y..(y + N), h w ≤ ∑ k ∈ Finset.range N, h (y + k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hadd : ∫ w in y..(y + ((N + 1 : ℕ) : ℝ)), h w =
          (∫ w in y..(y + N), h w) + ∫ w in (y + N)..(y + ((N + 1 : ℕ) : ℝ)), h w :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_h.intervalIntegrable _ _) (hcont_h.intervalIntegrable _ _)).symm
      have hcell : ∫ w in (y + N)..(y + ((N + 1 : ℕ) : ℝ)), h w ≤ h (y + N) := by
        have hle_pt : ∀ w ∈ Set.Icc (y + N) (y + ((N + 1 : ℕ) : ℝ)), h w ≤ h (y + N) := by
          intro w hw
          exact hant (by simp) (by simp only [Set.mem_Ici]; linarith [hw.1]) hw.1
        have hi := intervalIntegral.integral_mono_on (by push_cast; linarith)
          (hcont_h.intervalIntegrable (μ := volume) _ _) (intervalIntegrable_const (μ := volume)) hle_pt
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
        have hwidth : y + ((N + 1 : ℕ) : ℝ) - (y + N) = 1 := by push_cast; ring
        rw [hwidth, one_mul] at hi
        exact hi
      linarith
  have hint_id : ∀ N : ℕ,
      ∫ w in y..(y + N), h w =
        (∫ v in (y - δ)..(y + δ), Real.exp (-v ^ 2 * t)) -
        (∫ v in (y + N - δ)..(y + N + δ), Real.exp (-v ^ 2 * t)) := by
    intro N
    have hcont_f : Continuous (fun v : ℝ => Real.exp (-v ^ 2 * t)) := by fun_prop
    have hsub : ∫ w in y..(y + N), h w =
        (∫ w in y..(y + N), Real.exp (-(w - δ) ^ 2 * t)) -
        (∫ w in y..(y + N), Real.exp (-(w + δ) ^ 2 * t)) :=
      intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [hsub]
    have hl : ∫ w in y..(y + N), Real.exp (-(w - δ) ^ 2 * t) =
        ∫ v in (y - δ)..(y + N - δ), Real.exp (-v ^ 2 * t) := by
      simpa only [sub_eq_add_neg] using
        intervalIntegral.integral_comp_add_right (fun v : ℝ => Real.exp (-v ^ 2 * t)) (-δ)
    have hr : ∫ w in y..(y + N), Real.exp (-(w + δ) ^ 2 * t) =
        ∫ v in (y + δ)..(y + N + δ), Real.exp (-v ^ 2 * t) :=
      intervalIntegral.integral_comp_add_right (fun v : ℝ => Real.exp (-v ^ 2 * t)) δ
    rw [hl, hr]
    have hs1 : ∫ v in (y - δ)..(y + N + δ), Real.exp (-v ^ 2 * t) =
        (∫ v in (y - δ)..(y + δ), Real.exp (-v ^ 2 * t)) +
        ∫ v in (y + δ)..(y + N + δ), Real.exp (-v ^ 2 * t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)).symm
    have hs2 : ∫ v in (y - δ)..(y + N + δ), Real.exp (-v ^ 2 * t) =
        (∫ v in (y - δ)..(y + N - δ), Real.exp (-v ^ 2 * t)) +
        ∫ v in (y + N - δ)..(y + N + δ), Real.exp (-v ^ 2 * t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)).symm
    linarith
  have htend_int : Tendsto (fun N : ℕ => ∫ w in y..(y + N), h w) atTop
      (𝓝 (∫ v in (y - δ)..(y + δ), Real.exp (-v ^ 2 * t))) := by
    have htend_tail : Tendsto (fun N : ℕ => ∫ v in (y + N - δ)..(y + N + δ), Real.exp (-v ^ 2 * t)) atTop (𝓝 0) := by
      have hbd : ∀ N : ℕ, ‖∫ v in (y + N - δ)..(y + N + δ), Real.exp (-v ^ 2 * t)‖ ≤
          (2 * δ) * Real.exp (-(y + N - δ) ^ 2 * t) := by
        intro N
        have hpos : 0 ≤ ∫ v in (y + N - δ)..(y + N + δ), Real.exp (-v ^ 2 * t) :=
          intervalIntegral.integral_nonneg (by linarith) fun v _ => (Real.exp_pos _).le
        rw [Real.norm_of_nonneg hpos]
        have hpt : ∀ v ∈ Set.Icc (y + N - δ) (y + N + δ),
            Real.exp (-v ^ 2 * t) ≤ Real.exp (-(y + N - δ) ^ 2 * t) := by
          intro v hv
          have hv0 : 0 ≤ y + N - δ := by linarith [hyδ]
          have hsq : (y + N - δ) ^ 2 ≤ v ^ 2 := by nlinarith only [hv0, hv.1]
          exact Real.exp_le_exp.mpr (by nlinarith only [hsq, ht])
        have hi := intervalIntegral.integral_mono_on (by linarith)
          (Continuous.intervalIntegrable (μ := volume) (by fun_prop) _ _) (intervalIntegrable_const (μ := volume)) hpt
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
        linarith [show y + N + δ - (y + N - δ) = 2 * δ by ring]
      have htend_exp : Tendsto (fun N : ℕ => (2 * δ) * Real.exp (-(y + N - δ) ^ 2 * t)) atTop (𝓝 0) := by
        have hzero : (2 * δ : ℝ) * 0 = 0 := mul_zero _
        rw [← hzero]
        refine (tendsto_exp_atBot.comp ?_).const_mul (2 * δ)
        have hnat : Tendsto (fun N : ℕ => y + (N : ℝ) - δ) atTop atTop :=
          (tendsto_atTop_add_const_left atTop (y - δ) tendsto_natCast_atTop_atTop).congr
            fun N => by ring
        exact (tendsto_neg_atTop_atBot.comp
          ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_mul_const ht)).comp hnat |>.congr fun N => by
          dsimp [Function.comp_def]; ring
      exact squeeze_zero_norm' (Eventually.of_forall hbd) htend_exp
    have hc : Tendsto (fun N : ℕ =>
        (∫ v in (y - δ)..(y + δ), Real.exp (-v ^ 2 * t)) -
        (∫ v in (y + N - δ)..(y + N + δ), Real.exp (-v ^ 2 * t))) atTop
        (𝓝 (∫ v in (y - δ)..(y + δ), Real.exp (-v ^ 2 * t))) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub htend_tail
    exact hc.congr fun N => (hint_id N).symm
  exact le_of_tendsto_of_tendsto htend_int hs.hasSum.tendsto_sum_nat (Eventually.of_forall hstep)

private lemma gaussian_integral_ge_tangent {y δ t : ℝ} (hyδ : 0 ≤ y - δ) (hδ : 0 < δ)
    (ht : 0 < t) (hcond : 1 ≤ 2 * (y - δ) ^ 2 * t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤ ∫ v in (y - δ)..(y + δ), Real.exp (-v ^ 2 * t) := by
  let f : ℝ → ℝ := fun v => Real.exp (-v ^ 2 * t)
  let f' : ℝ → ℝ := fun v => -2 * v * t * Real.exp (-v ^ 2 * t)
  have hf_der : ∀ v, HasDerivAt f (f' v) v := by
    intro v
    have hp : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * v * t) v :=
      (((hasDerivAt_pow 2 v).fun_neg).mul_const t).congr_deriv (by ring)
    exact hp.exp.congr_deriv (by dsimp [f']; ring)
  have hf'_der : ∀ v, HasDerivAt f' (2 * t * (2 * v ^ 2 * t - 1) * Real.exp (-v ^ 2 * t)) v := by
    intro v
    have h1 : HasDerivAt (fun x : ℝ => -2 * x * t) (-2 * t) v := by
      have hid : HasDerivAt (fun x : ℝ => x) 1 v := hasDerivAt_id v
      exact ((hid.const_mul (-2 : ℝ)).mul_const t).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (f' v) v := hf_der v
    exact (h1.fun_mul h2).congr_deriv (by dsimp [f']; ring)
  have hf'_mono : MonotoneOn f' (Set.Icc (y - δ) (y + δ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (by dsimp [f']; fun_prop : Continuous f').continuousOn
    · exact fun v _ => (hf'_der v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hf'_der v).deriv]
      have hv2 : (y - δ) ^ 2 ≤ v ^ 2 := by nlinarith only [hyδ, hv.1]
      have hc : 1 ≤ 2 * v ^ 2 * t := by nlinarith only [hv2, hcond, ht]
      exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (Real.exp_pos _).le
  have hpt : ∀ v ∈ Set.Icc (y - δ) (y + δ),
      Real.exp (-y ^ 2 * t) + f' y * (v - y) ≤ f v := by
    intro v hv
    let g : ℝ → ℝ := fun x => f x - (Real.exp (-y ^ 2 * t) + f' y * (x - y))
    have hg_der : ∀ x, HasDerivAt g (f' x - f' y) x := by
      intro x
      have hl : HasDerivAt (fun u : ℝ => Real.exp (-y ^ 2 * t) + f' y * (u - y)) (f' y) x := by
        have hu : HasDerivAt (fun u : ℝ => f' y * (u - y)) (f' y) x := by
          simpa using ((hasDerivAt_id x).sub_const y).const_mul (f' y)
        simpa using (hasDerivAt_const x (Real.exp (-y ^ 2 * t))).fun_add hu
      exact ((hf_der x).fun_sub hl).congr_deriv (by ring)
    have hy_in : y ∈ Set.Icc (y - δ) (y + δ) := ⟨by linarith, by linarith⟩
    have hg0 : g y = 0 := by dsimp [g, f]; ring
    by_cases hvy : y ≤ v
    · have hmono : MonotoneOn g (Set.Icc y (y + δ)) :=
        monotoneOn_of_deriv_nonneg (convex_Icc _ _)
          (by dsimp [g, f]; fun_prop : Continuous g).continuousOn
          (fun x _ => (hg_der x).differentiableAt.differentiableWithinAt)
          fun x hx => by
            rw [interior_Icc] at hx
            rw [(hg_der x).deriv]
            have hm := hf'_mono hy_in ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
            linarith
      have hgv := hmono ⟨le_rfl, by linarith⟩ ⟨hvy, hv.2⟩ hvy
      dsimp [g] at hgv; linarith
    · have hvy' : v ≤ y := le_of_not_ge hvy
      have hant : AntitoneOn g (Set.Icc (y - δ) y) :=
        antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          (by dsimp [g, f]; fun_prop : Continuous g).continuousOn
          (fun x _ => (hg_der x).differentiableAt.differentiableWithinAt)
          fun x hx => by
            rw [interior_Icc] at hx
            rw [(hg_der x).deriv]
            have hm := hf'_mono ⟨hx.1.le, by linarith [hx.2]⟩ hy_in hx.2.le
            linarith
      have hgv := hant ⟨hv.1, hvy'⟩ ⟨by linarith, le_rfl⟩ hvy'
      dsimp [g] at hgv; linarith
  have hi := intervalIntegral.integral_mono_on (by linarith)
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (y - δ) (y + δ))
    (Continuous.intervalIntegrable (μ := volume) (by dsimp [f]; fun_prop) (y - δ) (y + δ)) hpt
  have hlin_int : ∫ v in (y - δ)..(y + δ), (Real.exp (-y ^ 2 * t) + f' y * (v - y)) =
      2 * δ * Real.exp (-y ^ 2 * t) := by
    have hftc : ∫ v in (y - δ)..(y + δ), (Real.exp (-y ^ 2 * t) + f' y * (v - y)) =
        ((fun v => Real.exp (-y ^ 2 * t) * v + f' y * (v - y) ^ 2 / 2) (y + δ)) -
        ((fun v => Real.exp (-y ^ 2 * t) * v + f' y * (v - y) ^ 2 / 2) (y - δ)) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun v => Real.exp (-y ^ 2 * t) * v + f' y * (v - y) ^ 2 / 2)
        (fun v _ => ?_)
        (Continuous.intervalIntegrable (μ := volume)
          (by fun_prop : Continuous (fun v : ℝ => Real.exp (-y ^ 2 * t) + f' y * (v - y))) (y - δ) (y + δ))
      have hid : HasDerivAt (fun x : ℝ => x) 1 v := hasDerivAt_id v
      have h1 := hid.const_mul (Real.exp (-y ^ 2 * t))
      have h2 := (((hid.sub_const y).pow 2).const_mul (f' y)).div_const 2
      exact (h1.fun_add h2).congr_deriv (by ring)
    rw [hftc]; ring
  linarith


private lemma gaussian_sum_ge_1a {y δ t : ℝ} (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (ht : 0 < t) (h1a : 3 / 4 ≤ y * t)
    (hs_all : Summable (fun k : ℕ => Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t))) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  have hk0 : Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y + δ) ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
    have hmem := Summable.le_tsum hs_all 0 (fun k _ => h_gauss_nonneg (by linarith) hδ0.le ht.le)
    simpa only [Nat.cast_zero, add_zero] using hmem
  refine le_trans ?_ hk0
  set u := 4 * y * δ * t
  have hu : 0 < u := by dsimp [u]; positivity
  have hfac : Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y + δ) ^ 2 * t) =
      Real.exp (-y ^ 2 * t) * Real.exp (δ * (2 * y - δ) * t) * (1 - Real.exp (-u)) := by
    have h1 : -y ^ 2 * t + δ * (2 * y - δ) * t = -(y - δ) ^ 2 * t := by ring
    have h2 : -(y - δ) ^ 2 * t + -u = -(y + δ) ^ 2 * t := by dsimp [u]; ring
    calc Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y + δ) ^ 2 * t)
        = Real.exp (-(y - δ) ^ 2 * t) * (1 - Real.exp (-u)) := by
            rw [mul_sub, mul_one, ← Real.exp_add, h2]
      _ = Real.exp (-y ^ 2 * t) * Real.exp (δ * (2 * y - δ) * t) * (1 - Real.exp (-u)) := by
            rw [← Real.exp_add, h1]
  rw [hfac]
  have hA_ge : u / 4 ≤ δ * (2 * y - δ) * t := by
    have h1 : δ * (2 * y - δ) * t - u / 4 = δ * (y - δ) * t := by dsimp [u]; ring
    have h2 : 0 ≤ δ * (y - δ) * t := mul_nonneg (mul_nonneg hδ0.le (by linarith only [hy, hδ_le])) ht.le
    linarith only [h1, h2]
  have hcoef : 2 * δ ≤ Real.exp (δ * (2 * y - δ) * t) * (1 - Real.exp (-u)) := by
    by_cases hu1 : 1 ≤ u
    · have hexp_neg1 : Real.exp (-u) ≤ 2 / 5 := by
        have hle : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith only [hu1])
        have hp2 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
          have := exp_ge_poly2 (by norm_num : (0 : ℝ) ≤ 1)
          linarith only [this]
        have hinv : Real.exp (-1) ≤ 2 / 5 := by
          rw [Real.exp_neg, show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num]
          exact inv_anti₀ (by norm_num) hp2
        exact le_trans hle hinv
      have hexpA : 1 ≤ Real.exp (δ * (2 * y - δ) * t) :=
        Real.one_le_exp (le_trans (by linarith only [hu]) hA_ge)
      have h1e : (3 / 5 : ℝ) ≤ 1 - Real.exp (-u) := by linarith only [hexp_neg1]
      have h2d : 2 * δ ≤ 3 / 5 := by linarith only [hδ_le]
      nlinarith only [hexpA, h1e, h2d]
    · have hu_lt : u < 1 := lt_of_not_ge hu1
      have hexpA : 1 + u / 4 ≤ Real.exp (δ * (2 * y - δ) * t) :=
        le_trans (by linarith only [hA_ge]) (Real.add_one_le_exp (δ * (2 * y - δ) * t))
      have h1e := one_sub_exp_neg_ge hu.le
      have h2d : 2 * δ ≤ (2 / 3) * u := by
        have hu_eq : (2 / 3) * u = (8 / 3 * (y * t)) * δ := by dsimp [u]; ring
        have hm : 2 * δ ≤ (8 / 3 * (y * t)) * δ := by nlinarith only [h1a, hδ0]
        linarith only [hu_eq, hm]
      have hpoly : (2 / 3) * u ≤ (1 + u / 4) * ((u + u ^ 2 / 2) / (1 + u + u ^ 2 / 2)) := by
        have hpos : 0 < 1 + u + u ^ 2 / 2 := by positivity
        rw [← sub_nonneg]
        have heq : (1 + u / 4) * ((u + u ^ 2 / 2) / (1 + u + u ^ 2 / 2)) - (2 / 3) * u =
            u * (1 / 3 + u / 12 - 5 / 24 * u ^ 2) / (1 + u + u ^ 2 / 2) := by
          field_simp [hpos.ne']; ring
        rw [heq]
        have hu2 : u ^ 2 ≤ u := by nlinarith only [hu, hu_lt]
        have hq : 0 ≤ 1 / 3 + u / 12 - 5 / 24 * u ^ 2 := by nlinarith only [hu, hu_lt, hu2]
        exact div_nonneg (mul_nonneg hu.le hq) hpos.le
      have hprod := mul_le_mul hexpA h1e (by positivity) (by positivity)
      linarith only [h2d, hpoly, hprod]
  have hmul := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-y ^ 2 * t)).le
  linarith only [hmul, show 2 * δ * Real.exp (-y ^ 2 * t) =
      2 * δ * Real.exp (-y ^ 2 * t) by ring,
    show Real.exp (δ * (2 * y - δ) * t) * (1 - Real.exp (-u)) * Real.exp (-y ^ 2 * t) =
      Real.exp (-y ^ 2 * t) * Real.exp (δ * (2 * y - δ) * t) * (1 - Real.exp (-u)) by ring]

private lemma gaussian_sum_ge_1c_largeY {y δ t : ℝ} (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (ht : 0 < t) (hy : 6 / 5 ≤ y) (hyt : y * t < 3 / 4) (h1b : 2 * (y - δ) ^ 2 * t < 1) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  set a₀ := y - 1 / 2
  have hp3 := P3_gauss_bounds a₀ δ t hδ0 ht
  have htsum_eq : (∑' k : ℕ, (Real.exp (-(a₀ + 1 / 2 + k - δ) ^ 2 * t) -
      Real.exp (-(a₀ + 1 / 2 + k + δ) ^ 2 * t))) =
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
    refine tsum_congr (fun k => ?_); dsimp [a₀]; ring_nf
  have ha_lo : 0 ≤ a₀ - δ := by dsimp [a₀]; linarith only [hy, hδ_le]
  have ha_hi : a₀ + δ ≤ y - δ := by dsimp [a₀]; linarith only [hδ_le]
  have hp_nn : 0 ≤ -2 * (a₀ - δ) * t * Real.exp (-(a₀ - δ) ^ 2 * t) +
      2 * (a₀ + δ) * t * Real.exp (-(a₀ + δ) ^ 2 * t) := by
    let g : ℝ → ℝ := fun u => u * Real.exp (-u ^ 2 * t)
    have hg_der : ∀ u, HasDerivAt g ((1 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t)) u := by
      intro u
      have harg : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
        (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
      exact ((hasDerivAt_id u).fun_mul harg.exp).congr_deriv (by simp; ring)
    have hg_mono : MonotoneOn g (Set.Icc (a₀ - δ) (a₀ + δ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact (by dsimp [g]; fun_prop : Continuous g).continuousOn
      · exact fun u _ => (hg_der u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hg_der u).deriv]
        have hu2 : u ^ 2 ≤ (y - δ) ^ 2 := by nlinarith only [ha_lo, ha_hi, hu.1, hu.2]
        have hcond : 2 * u ^ 2 * t ≤ 1 := by nlinarith only [hu2, h1b, ht]
        exact mul_nonneg (by linarith only [hcond]) (Real.exp_pos _).le
    have hle := hg_mono ⟨le_rfl, by linarith only [hδ0]⟩ ⟨by linarith only [hδ0], le_rfl⟩
      (by linarith only [hδ0])
    dsimp [g] at hle
    nlinarith only [hle, ht]
  have hI_lb : 2 * δ * Real.exp (-y ^ 2 * t) * (1 + 43 / 80 * t) ≤
      ∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t) := by
    have hpt : ∀ v ∈ Set.Icc (a₀ - δ) (a₀ + δ),
        Real.exp (-y ^ 2 * t) * (1 + 43 / 80 * t) ≤ Real.exp (-v ^ 2 * t) := by
      intro v hv
      have hv_nn : 0 ≤ v := le_trans ha_lo hv.1
      have hv_ub : v ≤ y - 1 / 4 := by
        have : a₀ + δ ≤ y - 1 / 4 := by dsimp [a₀]; linarith only [hδ_le]
        linarith only [hv.2, this]
      have hy2_gap : 43 / 80 ≤ y ^ 2 - v ^ 2 := by
        have hv2 : v ^ 2 ≤ (y - 1 / 4) ^ 2 := pow_le_pow_left₀ hv_nn hv_ub 2
        nlinarith only [hy, hv2]
      have hexp : 1 + 43 / 80 * t ≤ Real.exp ((y ^ 2 - v ^ 2) * t) :=
        le_trans (by nlinarith only [hy2_gap, ht]) (Real.add_one_le_exp ((y ^ 2 - v ^ 2) * t))
      have heq : Real.exp (-y ^ 2 * t) * Real.exp ((y ^ 2 - v ^ 2) * t) = Real.exp (-v ^ 2 * t) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (-y ^ 2 * t) * (1 + 43 / 80 * t)
          ≤ Real.exp (-y ^ 2 * t) * Real.exp ((y ^ 2 - v ^ 2) * t) :=
            mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
        _ = Real.exp (-v ^ 2 * t) := heq
    have hi := intervalIntegral.integral_mono_on (by linarith only [hδ0])
      (intervalIntegrable_const (μ := volume))
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ)) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    have hlen : (a₀ + δ) - (a₀ - δ) = 2 * δ := by ring
    rw [hlen] at hi
    linarith only [hi]
  have hsqrt : Real.sqrt t ≤ 4 / 5 := by
    have ht_ub : t ≤ 5 / 8 := by nlinarith only [hy, hyt]
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, by linarith only [ht_ub]⟩
  have hexp_y2 : Real.exp (y ^ 2 * t) ≤ 100 / 43 := by
    have hy_sub : 19 * y ≤ 24 * (y - δ) := by linarith only [hy, hδ_le]
    have hsq : 361 * y ^ 2 ≤ 576 * (y - δ) ^ 2 := by nlinarith only [hy, hy_sub]
    have hy2t : y ^ 2 * t ≤ 4 / 5 := by
      have : 361 * (y ^ 2 * t) < 288 := by nlinarith only [hsq, h1b, ht]
      linarith only [this]
    have hexp_neg : 43 / 100 ≤ Real.exp (-(y ^ 2 * t)) := by
      have h1 := exp_neg_ge_poly3 (by norm_num : (0 : ℝ) ≤ 4 / 5)
      have h2 := Real.exp_le_exp.mpr (by linarith only [hy2t] : -(4 / 5 : ℝ) ≤ -(y ^ 2 * t))
      linarith only [h1, h2]
    rw [← inv_inv (Real.exp (y ^ 2 * t)), ← Real.exp_neg, show (100 / 43 : ℝ) = (43 / 100)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) hexp_neg
  have herr_cmp : (11 / 60 : ℝ) * (2 * δ) * t * Real.sqrt t ≤
      (43 / 80 : ℝ) * t * (2 * δ * Real.exp (-y ^ 2 * t)) := by
    have h1 : (11 / 60 : ℝ) * Real.sqrt t * Real.exp (y ^ 2 * t) ≤ 43 / 80 := by
      have hm := mul_le_mul hsqrt hexp_y2 (Real.exp_pos _).le (by norm_num)
      linarith only [hm]
    have hm2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * δ * t)) (Real.exp_pos (-y ^ 2 * t)).le
    have hcan : 2 * δ * t * (11 / 60 * Real.sqrt t * Real.exp (y ^ 2 * t)) * Real.exp (-y ^ 2 * t) =
        11 / 60 * (2 * δ) * t * Real.sqrt t := by
      have hadd : Real.exp (y ^ 2 * t) * Real.exp (-y ^ 2 * t) = 1 := by
        rw [← Real.exp_add, show y ^ 2 * t + -y ^ 2 * t = 0 by ring, Real.exp_zero]
      calc 2 * δ * t * (11 / 60 * Real.sqrt t * Real.exp (y ^ 2 * t)) * Real.exp (-y ^ 2 * t)
          = 11 / 60 * (2 * δ) * t * Real.sqrt t * (Real.exp (y ^ 2 * t) * Real.exp (-y ^ 2 * t)) := by ring
        _ = 11 / 60 * (2 * δ) * t * Real.sqrt t := by rw [hadd, mul_one]
    linarith only [hm2, hcan]
  have habs := (abs_le.mp hp3.2).1
  rw [htsum_eq] at habs
  linarith only [habs, hI_lb, hp_nn, herr_cmp]

private lemma gaussian_f3_integral_abs_le {a b t M4 E : ℝ} (hab : a ≤ b) (_ht : 0 ≤ t)
    (hM4 : ∀ u ∈ Set.Icc a b, |4 * (u ^ 2 * t) ^ 2 - 12 * (u ^ 2 * t) + 3| ≤ M4)
    (hE : ∀ u ∈ Set.Icc a b, Real.exp (-u ^ 2 * t) ≤ E) :
    |-4 * t ^ 2 * a * (2 * a ^ 2 * t - 3) * Real.exp (-a ^ 2 * t) -
      -4 * t ^ 2 * b * (2 * b ^ 2 * t - 3) * Real.exp (-b ^ 2 * t)| ≤
      (b - a) * (4 * t ^ 2 * M4 * E) := by
  let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * (2 * u ^ 3 * t - 3 * u) * Real.exp (-u ^ 2 * t)
  let f4 : ℝ → ℝ := fun u => 4 * t ^ 2 * (4 * u ^ 4 * t ^ 2 - 12 * u ^ 2 * t + 3) * Real.exp (-u ^ 2 * t)
  have hf4 : ∀ u, HasDerivAt f3 (f4 u) u := by
    intro u
    have h1 : HasDerivAt (fun x : ℝ => -4 * t ^ 2 * (2 * x ^ 3 * t - 3 * x))
        (-4 * t ^ 2 * (6 * u ^ 2 * t - 3)) u := by
      have hp3 := ((hasDerivAt_pow 3 u).const_mul (2 : ℝ)).mul_const t
      have hlin := (hasDerivAt_id' u).const_mul (3 : ℝ)
      refine ((hp3.fun_sub hlin).const_mul (-4 * t ^ 2)).congr_deriv ?_
      push_cast; ring
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (-2 * u * t * Real.exp (-u ^ 2 * t)) u := by
      have harg : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
        (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
      exact harg.exp.congr_deriv (by ring)
    exact (h1.fun_mul h2).congr_deriv (by dsimp [f4]; ring)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := f3) (a := a) (b := b)
    (fun u _ => hf4 u) (Continuous.intervalIntegrable (μ := volume) (by dsimp [f4]; fun_prop) a b)
  have hbd : ∀ u ∈ Set.Icc a b, |f4 u| ≤ 4 * t ^ 2 * M4 * E := by
    intro u hu
    have hq := hM4 u hu
    have hex := hE u hu
    have hM4_nn : 0 ≤ M4 := le_trans (abs_nonneg _) (hM4 a ⟨le_rfl, hab⟩)
    have hmul : 4 * t ^ 2 * |4 * (u ^ 2 * t) ^ 2 - 12 * (u ^ 2 * t) + 3| * Real.exp (-u ^ 2 * t) ≤
        4 * t ^ 2 * M4 * E :=
      mul_le_mul (mul_le_mul_of_nonneg_left hq (by positivity)) hex (Real.exp_pos _).le (by positivity)
    have heq : |f4 u| = 4 * t ^ 2 * |4 * (u ^ 2 * t) ^ 2 - 12 * (u ^ 2 * t) + 3| * Real.exp (-u ^ 2 * t) := by
      dsimp [f4]
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * t ^ 2), abs_of_pos (Real.exp_pos _)]
      congr 1; congr 1; ring
    exact heq ▸ hmul
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := 4 * t ^ 2 * M4 * E) (f := f4) fun u hu => by
    rw [Real.norm_eq_abs]
    rw [Set.uIoc_of_le hab] at hu
    exact hbd u ⟨hu.1.le, hu.2⟩
  rw [hftc, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm _ (b - a)] at hi
  have hf3_eq : ∀ w : ℝ, -4 * t ^ 2 * (2 * w ^ 3 * t - 3 * w) * Real.exp (-w ^ 2 * t) =
      -4 * t ^ 2 * w * (2 * w ^ 2 * t - 3) * Real.exp (-w ^ 2 * t) := fun w => by ring
  dsimp [f3] at hi
  rwa [hf3_eq a, hf3_eq b] at hi

private lemma gaussian_sum_ge_1c_smallT {y δ t : ℝ} (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (ht : 0 < t) (hy_ub : y < 6 / 5) (ht_ub : t ≤ 7 / 10)
    (hyt : y * t < 3 / 4) (h1b : 2 * (y - δ) ^ 2 * t < 1) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  set a₀ := y - 1 / 2
  have hp5 := P5_gauss_bounds a₀ δ t hδ0 ht
  have htsum_eq : (∑' k : ℕ, (Real.exp (-(a₀ + 1 / 2 + k - δ) ^ 2 * t) -
      Real.exp (-(a₀ + 1 / 2 + k + δ) ^ 2 * t))) =
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
    refine tsum_congr (fun k => ?_); dsimp [a₀]; ring_nf
  have hI_lb : 2 * δ * Real.exp (-y ^ 2 * t) * (1 + (y - 1 / 4 - δ ^ 2 / 3) * t) ≤
      ∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t) := by
    have hpt : ∀ v ∈ Set.Icc (a₀ - δ) (a₀ + δ),
        Real.exp (-y ^ 2 * t) * (1 + (y ^ 2 - v ^ 2) * t) ≤ Real.exp (-v ^ 2 * t) := by
      intro v _
      have hexp : 1 + (y ^ 2 - v ^ 2) * t ≤ Real.exp ((y ^ 2 - v ^ 2) * t) := by
        linarith only [Real.add_one_le_exp ((y ^ 2 - v ^ 2) * t)]
      have heq : Real.exp (-y ^ 2 * t) * Real.exp ((y ^ 2 - v ^ 2) * t) = Real.exp (-v ^ 2 * t) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (-y ^ 2 * t) * (1 + (y ^ 2 - v ^ 2) * t)
          ≤ Real.exp (-y ^ 2 * t) * Real.exp ((y ^ 2 - v ^ 2) * t) :=
            mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
        _ = Real.exp (-v ^ 2 * t) := heq
    have hi := intervalIntegral.integral_mono_on (by linarith only [hδ0])
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ))
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ)) hpt
    have hint_poly : ∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-y ^ 2 * t) * (1 + (y ^ 2 - v ^ 2) * t) =
        2 * δ * Real.exp (-y ^ 2 * t) * (1 + (y - 1 / 4 - δ ^ 2 / 3) * t) := by
      have ha : ∀ v, HasDerivAt (fun x : ℝ => Real.exp (-y ^ 2 * t) * (x + (y ^ 2 * x - x ^ 3 / 3) * t))
          (Real.exp (-y ^ 2 * t) * (1 + (y ^ 2 - v ^ 2) * t)) v := by
        intro v
        have h1 := hasDerivAt_id' v
        have h2 := (((hasDerivAt_id' v).const_mul (y ^ 2)).fun_sub ((hasDerivAt_pow 3 v).div_const 3)).mul_const t
        have hd : HasDerivAt (fun x : ℝ => x + (y ^ 2 * x - x ^ 3 / 3) * t) (1 + (y ^ 2 - v ^ 2) * t) v := by
          refine (h1.fun_add h2).congr_deriv ?_
          push_cast; ring
        exact hd.const_mul (Real.exp (-y ^ 2 * t))
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => ha v)
        (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ))
      rw [hftc]; dsimp [a₀]; ring
    linarith only [hi, hint_poly]
  have hv_sq_bd : ∀ v ∈ Set.Icc (a₀ - δ) (a₀ + δ), 2 * v ^ 2 * t ≤ 1 := by
    intro v hv
    by_cases hv0 : 0 ≤ v
    · have hv_hi : v ≤ y - δ := by
        have : a₀ + δ ≤ y - δ := by dsimp [a₀]; linarith only [hδ_le]
        linarith only [hv.2, this]
      have hv2 : v ^ 2 ≤ (y - δ) ^ 2 := pow_le_pow_left₀ hv0 hv_hi 2
      nlinarith only [hv2, h1b, ht]
    · have hv_lo : -(1 / 2 : ℝ) ≤ v := by dsimp [a₀] at hv; linarith only [hy, hδ_le, hv.1]
      have hv2 : v ^ 2 ≤ 1 / 4 := by nlinarith only [hv_lo, hv0]
      nlinarith only [hv2, ht_ub, ht]
  have hp_lb : 2 * δ * Real.exp (-y ^ 2 * t) * (2 * t * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t)) ≤
      -2 * (a₀ - δ) * t * Real.exp (-(a₀ - δ) ^ 2 * t) +
        2 * (a₀ + δ) * t * Real.exp (-(a₀ + δ) ^ 2 * t) := by
    let g : ℝ → ℝ := fun u => u * Real.exp (-u ^ 2 * t)
    have hg_der : ∀ u, HasDerivAt g ((1 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t)) u := by
      intro u
      have harg : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
        (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
      exact ((hasDerivAt_id u).fun_mul harg.exp).congr_deriv (by simp; ring)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g) (a := a₀ - δ) (b := a₀ + δ)
      (fun u _ => hg_der u)
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ))
    have hpt : ∀ u ∈ Set.Icc (a₀ - δ) (a₀ + δ), 1 - 3 * u ^ 2 * t ≤ (1 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t) := by
      intro u hu
      have hc := hv_sq_bd u hu
      have he := exp_neg_ge_poly1 (x := u ^ 2 * t)
      rw [show -(u ^ 2 * t) = -u ^ 2 * t by ring] at he
      have hm := mul_le_mul_of_nonneg_left he (by linarith only [hc] : 0 ≤ 1 - 2 * u ^ 2 * t)
      have hsq : 0 ≤ 2 * u ^ 4 * t ^ 2 := by positivity
      have hexp : (1 - 2 * u ^ 2 * t) * (1 - u ^ 2 * t) = 1 - 3 * u ^ 2 * t + 2 * u ^ 4 * t ^ 2 := by ring
      linarith only [hm, hsq, hexp]
    have hi := intervalIntegral.integral_mono_on (by linarith only [hδ0])
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ))
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ)) hpt
    have hint_poly : ∫ u in (a₀ - δ)..(a₀ + δ), (1 - 3 * u ^ 2 * t) = 2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) := by
      have hd : ∀ u, HasDerivAt (fun x : ℝ => x - x ^ 3 * t) (1 - 3 * u ^ 2 * t) u := fun u => by
        refine ((hasDerivAt_id' u).fun_sub ((hasDerivAt_pow 3 u).mul_const t)).congr_deriv ?_
        push_cast; ring
      have hftc2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
        (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (a₀ - δ) (a₀ + δ))
      rw [hftc2]; ring
    have hg_diff : 2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) ≤ g (a₀ + δ) - g (a₀ - δ) := by
      linarith only [hftc, hi, hint_poly]
    have hnonneg : 0 ≤ 1 - (3 * a₀ ^ 2 + δ ^ 2) * t := by
      by_cases hy1 : y ≤ 1
      · have ha2 : a₀ ^ 2 ≤ 1 / 4 := by dsimp [a₀]; nlinarith only [hy, hy1]
        have hd2 : δ ^ 2 ≤ 1 / 16 := by nlinarith only [hδ0, hδ_le]
        have h3a : 3 * a₀ ^ 2 + δ ^ 2 ≤ 13 / 16 := by linarith only [ha2, hd2]
        have hnn : 0 ≤ 3 * a₀ ^ 2 + δ ^ 2 := by positivity
        nlinarith only [h3a, hnn, ht_ub, ht]
      · have hy_gt : 1 < y := lt_of_not_ge hy1
        have hd2 : δ ^ 2 ≤ 1 / 16 := by nlinarith only [hδ0, hδ_le]
        have hquad : 0 ≤ 9 * (6 / 5 - y) * (y - 1) := by nlinarith only [hy_gt, hy_ub]
        have h3a_y : 3 * (3 * a₀ ^ 2 + δ ^ 2) ≤ 4 * y := by
          dsimp [a₀]; nlinarith only [hquad, hd2, hy_ub]
        have h3at : 3 * ((3 * a₀ ^ 2 + δ ^ 2) * t) ≤ 4 * (y * t) := by nlinarith only [h3a_y, ht]
        linarith only [h3at, hyt]
    have hexp_le1 : Real.exp (-y ^ 2 * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg y, ht])
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_le1 hnonneg) (by positivity : 0 ≤ 2 * δ)
    have h2 : Real.exp (-y ^ 2 * t) * (2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t)) ≤ g (a₀ + δ) - g (a₀ - δ) := by
      have h1' : 2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) * Real.exp (-y ^ 2 * t) ≤
          2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) := by
        rw [show 2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) * Real.exp (-y ^ 2 * t) =
          2 * δ * ((1 - (3 * a₀ ^ 2 + δ ^ 2) * t) * Real.exp (-y ^ 2 * t)) by ring]
        rw [mul_one] at h1
        exact h1
      linarith only [h1', hg_diff, show Real.exp (-y ^ 2 * t) * (2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t)) =
        2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) * Real.exp (-y ^ 2 * t) by ring]
    dsimp [g] at h2
    have h2t := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * t)
    linarith only [h2t,
      show 2 * t * (Real.exp (-y ^ 2 * t) * (2 * δ * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t))) =
        2 * δ * Real.exp (-y ^ 2 * t) * (2 * t * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t)) by ring,
      show 2 * t * ((a₀ + δ) * Real.exp (-(a₀ + δ) ^ 2 * t) - (a₀ - δ) * Real.exp (-(a₀ - δ) ^ 2 * t)) =
        -2 * (a₀ - δ) * t * Real.exp (-(a₀ - δ) ^ 2 * t) + 2 * (a₀ + δ) * t * Real.exp (-(a₀ + δ) ^ 2 * t) by ring]
  have hh3_abs : |-4 * t ^ 2 * (a₀ - δ) * (2 * (a₀ - δ) ^ 2 * t - 3) * Real.exp (-(a₀ - δ) ^ 2 * t) -
      -4 * t ^ 2 * (a₀ + δ) * (2 * (a₀ + δ) ^ 2 * t - 3) * Real.exp (-(a₀ + δ) ^ 2 * t)| ≤
      2 * δ * (12 * t ^ 2) := by
    have hraw := gaussian_f3_integral_abs_le (a := a₀ - δ) (b := a₀ + δ) (t := t) (M4 := 3) (E := 1)
      (by linarith only [hδ0]) ht.le
      (fun u hu => by
        have hz0 : 0 ≤ u ^ 2 * t := by positivity
        have hz1 : u ^ 2 * t ≤ 1 / 2 := by linarith only [hv_sq_bd u hu]
        have h1 : (u ^ 2 * t) ^ 2 ≤ (u ^ 2 * t) * (1 / 2) := by
          rw [sq]; exact mul_le_mul_of_nonneg_left hz1 hz0
        rw [abs_le]; constructor <;> linarith only [hz0, hz1, h1, sq_nonneg (u ^ 2 * t)])
      (fun u _ => Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) ht.le))
    rw [show (a₀ + δ - (a₀ - δ)) * (4 * t ^ 2 * 3 * 1) = 2 * δ * (12 * t ^ 2) by ring] at hraw
    exact hraw
  have hsqrt_le : Real.sqrt t ≤ 17 / 20 := by
    rw [Real.sqrt_le_iff]; refine ⟨by norm_num, by linarith only [ht_ub]⟩
  have htsq_bd : 7 / 480 * t + 1 / 24 * t * Real.sqrt t ≤ 7 / 480 * (7 / 10) + 1 / 24 * (7 / 10) * (17 / 20) := by
    have ha : 1 / 24 * t * Real.sqrt t ≤ 1 / 24 * (7 / 10) * (17 / 20) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) hsqrt_le (Real.sqrt_nonneg _) (by norm_num)
    linarith only [ht_ub, ha]
  have htsq_nn : 0 ≤ 7 / 480 * t + 1 / 24 * t * Real.sqrt t := by positivity
  have hfin : (7 / 5760 : ℝ) * (2 * δ * (12 * t ^ 2)) + 1 / 24 * (2 * δ) * t ^ 2 * Real.sqrt t ≤
      2 * δ * Real.exp (-y ^ 2 * t) * ((y - 1 / 4 - δ ^ 2 / 3) * t +
        1 / 24 * (2 * t * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t))) := by
    by_cases hy12 : y ≤ 1 / 2
    · have hexp_bd : Real.exp (y ^ 2 * t) ≤ 6 / 5 := by
        have hy2 : y ^ 2 ≤ 1 / 4 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) hy12 2) (by norm_num)
        have hy2t : y ^ 2 * t ≤ 7 / 40 :=
          le_trans (mul_le_mul hy2 ht_ub ht.le (by norm_num)) (by norm_num)
        exact exp_ub_of_le (by norm_num) hy2t (by norm_num) (by norm_num)
      have herr_cmp : (7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t) ≤
          (y - 1 / 4 - δ ^ 2 / 3) + 1 / 12 * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) := by
        have hleft : (7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t) ≤
            (7 / 480 * (7 / 10) + 1 / 24 * (7 / 10) * (17 / 20)) * (6 / 5) :=
          mul_le_mul htsq_bd hexp_bd (Real.exp_pos _).le (by norm_num)
        have hd2 : δ ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hδ0.le hδ_le 2) (by norm_num)
        have ha2 : a₀ ^ 2 ≤ 1 / 16 := by
          dsimp [a₀]
          rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, sq_le_sq, abs_le]
          norm_num; constructor <;> linarith only [hy, hy12]
        have h3a : (3 * a₀ ^ 2 + δ ^ 2) * t ≤ (1 / 4 : ℝ) * (7 / 10) :=
          mul_le_mul (by linarith only [ha2, hd2]) ht_ub ht.le (by norm_num)
        have hright : (23 / 480 : ℝ) ≤ (y - 1 / 4 - δ ^ 2 / 3) + 1 / 12 * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) := by
          linarith only [hy, hd2, h3a]
        linarith only [hleft, hright]
      have hcan : 2 * δ * t * ((7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t)) * Real.exp (-y ^ 2 * t) =
          7 / 5760 * (2 * δ * (12 * t ^ 2)) + 1 / 24 * (2 * δ) * t ^ 2 * Real.sqrt t := by
        have hadd : Real.exp (y ^ 2 * t) * Real.exp (-y ^ 2 * t) = 1 := by
          rw [← Real.exp_add, show y ^ 2 * t + -y ^ 2 * t = 0 by ring, Real.exp_zero]
        rw [show 2 * δ * t * ((7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t)) * Real.exp (-y ^ 2 * t) =
          (7 / 5760 * (2 * δ * (12 * t ^ 2)) + 1 / 24 * (2 * δ) * t ^ 2 * Real.sqrt t) *
            (Real.exp (y ^ 2 * t) * Real.exp (-y ^ 2 * t)) by ring, hadd, mul_one]
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herr_cmp (by positivity : 0 ≤ 2 * δ * t)) (Real.exp_pos (-y ^ 2 * t)).le
      rw [← hcan]
      refine le_trans hm (le_of_eq ?_); ring
    · have hy_gt : 1 / 2 < y := lt_of_not_ge hy12
      have hexp_bd : Real.exp (y ^ 2 * t) ≤ 5 / 2 := by
        have hy2t : y ^ 2 * t ≤ 9 / 10 := by
          have hyy : y * (y * t) ≤ (6 / 5) * (3 / 4) :=
            mul_le_mul hy_ub.le hyt.le (mul_nonneg (by linarith only [hy]) ht.le) (by norm_num)
          linarith only [hyy, show y ^ 2 * t = y * (y * t) by ring]
        have he := exp_neg_ge_poly5 (by norm_num : (0 : ℝ) ≤ 9 / 10)
        have hm := Real.exp_le_exp.mpr (by linarith only [hy2t] : -(9 / 10 : ℝ) ≤ -(y ^ 2 * t))
        have hpos : (2 / 5 : ℝ) ≤ Real.exp (-(y ^ 2 * t)) := by linarith only [he, hm]
        rw [← inv_inv (Real.exp (y ^ 2 * t)), ← Real.exp_neg, show (5 / 2 : ℝ) = (2 / 5)⁻¹ by norm_num]
        exact inv_anti₀ (by norm_num) hpos
      have herr_cmp : (7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t) ≤
          (y - 1 / 4 - δ ^ 2 / 3) + 1 / 12 * (1 - (3 * a₀ ^ 2 + δ ^ 2) * t) := by
        have hleft : (7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t) ≤
            (7 / 480 * (7 / 10) + 1 / 24 * (7 / 10) * (17 / 20)) * (5 / 2) :=
          mul_le_mul htsq_bd hexp_bd (Real.exp_pos _).le (by norm_num)
        have h1_nonneg : 0 ≤ 1 - (3 * a₀ ^ 2 + δ ^ 2) * t := by
          have hd2 : δ ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hδ0.le hδ_le 2) (by norm_num)
          by_cases hy1 : y ≤ 1
          · have ha2' : a₀ ^ 2 ≤ 1 / 4 := by
              dsimp [a₀]
              exact le_trans (pow_le_pow_left₀ (by linarith only [hy_gt]) (by linarith only [hy1] : y - 1 / 2 ≤ 1 / 2) 2) (by norm_num)
            have h3a : (3 * a₀ ^ 2 + δ ^ 2) * t ≤ (13 / 16 : ℝ) * (7 / 10) :=
              mul_le_mul (by linarith only [ha2', hd2]) ht_ub ht.le (by norm_num)
            linarith only [h3a]
          · have hy_gt1 : 1 < y := lt_of_not_ge hy1
            have hquad : 0 ≤ 9 * (6 / 5 - y) * (y - 1) :=
              mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hy_ub])) (by linarith only [hy_gt1])
            have h3a_y : 3 * (3 * a₀ ^ 2 + δ ^ 2) ≤ 4 * y := by
              have ha0_eq : 9 * a₀ ^ 2 = 9 * y ^ 2 - 9 * y + 9 / 4 := by dsimp [a₀]; ring
              linarith only [hquad, hd2, ha0_eq, hy_ub, show 9 * (6 / 5 - y) * (y - 1) = -9 * y ^ 2 + 99 / 5 * y - 54 / 5 by ring]
            have h3at : 3 * ((3 * a₀ ^ 2 + δ ^ 2) * t) ≤ 4 * (y * t) := by
              rw [show 3 * ((3 * a₀ ^ 2 + δ ^ 2) * t) = (3 * (3 * a₀ ^ 2 + δ ^ 2)) * t by ring,
                  show 4 * (y * t) = (4 * y) * t by ring]
              exact mul_le_mul_of_nonneg_right h3a_y ht.le
            linarith only [h3at, hyt]
        have hd2 : δ ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hδ0.le hδ_le 2) (by norm_num)
        have hright : 1 / 4 - 1 / 48 ≤ y - 1 / 4 - δ ^ 2 / 3 := by linarith only [hy_gt, hd2]
        linarith only [hleft, hright, h1_nonneg]
      have hcan : 2 * δ * t * ((7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t)) * Real.exp (-y ^ 2 * t) =
          7 / 5760 * (2 * δ * (12 * t ^ 2)) + 1 / 24 * (2 * δ) * t ^ 2 * Real.sqrt t := by
        have hadd : Real.exp (y ^ 2 * t) * Real.exp (-y ^ 2 * t) = 1 := by
          rw [← Real.exp_add, show y ^ 2 * t + -y ^ 2 * t = 0 by ring, Real.exp_zero]
        rw [show 2 * δ * t * ((7 / 480 * t + 1 / 24 * t * Real.sqrt t) * Real.exp (y ^ 2 * t)) * Real.exp (-y ^ 2 * t) =
          (7 / 5760 * (2 * δ * (12 * t ^ 2)) + 1 / 24 * (2 * δ) * t ^ 2 * Real.sqrt t) *
            (Real.exp (y ^ 2 * t) * Real.exp (-y ^ 2 * t)) by ring, hadd, mul_one]
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herr_cmp (by positivity : 0 ≤ 2 * δ * t)) (Real.exp_pos (-y ^ 2 * t)).le
      rw [← hcan]
      refine le_trans hm (le_of_eq ?_); ring
  have habs := (abs_le.mp hp5.2).1
  have h3le := (abs_le.mp hh3_abs).2
  rw [htsum_eq] at habs
  linarith only [habs, hI_lb, hp_lb, h3le, hfin]


lemma gaussian_sum_ge_le_quarter_aux {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4) (ht : 0 < t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  have hs_all : Summable (fun k : ℕ => Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
    have hpb := (P5_gauss_bounds (y - 1 / 2) δ t hδ0 ht).1
    exact hpb.congr fun k => by ring_nf
  by_cases h1a : 3 / 4 ≤ y * t
  · exact gaussian_sum_ge_1a hy hδ0 hδ_le ht h1a hs_all
  · have h1a_neg : y * t < 3 / 4 := lt_of_not_ge h1a
    by_cases h1b : 1 ≤ 2 * (y - δ) ^ 2 * t
    · exact le_trans (gaussian_integral_ge_tangent (by linarith only [hy, hδ_le]) hδ0 ht h1b)
        (gaussian_antitone_sum_ge_integral (by linarith only [hy, hδ_le]) hδ0 ht h1b hs_all)
    · have h1b_neg : 2 * (y - δ) ^ 2 * t < 1 := lt_of_not_ge h1b
      by_cases hy65 : 6 / 5 ≤ y
      · exact gaussian_sum_ge_1c_largeY hδ0 hδ_le ht hy65 h1a_neg h1b_neg
      · have hy_lt65 : y < 6 / 5 := lt_of_not_ge hy65
        by_cases ht710 : t ≤ 7 / 10
        · exact gaussian_sum_ge_1c_smallT hy hδ0 hδ_le ht hy_lt65 ht710 h1a_neg h1b_neg
        · have ht_gt710 : 7 / 10 < t := lt_of_not_ge ht710
          have hy_le1110 : y ≤ 11 / 10 := by
            by_contra hy_gt1110; push Not at hy_gt1110
            have : 3 / 4 < y * t := by nlinarith only [hy_gt1110, ht_gt710]
            linarith only [this, h1a_neg]
          have ht_le3 : t ≤ 3 := by
            by_contra ht_gt3; push Not at ht_gt3
            have : 3 / 4 < y * t := by nlinarith only [hy, ht_gt3]
            linarith only [this, h1a_neg]
          exact RademacherGamma_gaussian_sum_ge_c1_box hy hy_le1110 hδ0 hδ_le ht_gt710 ht_le3 h1a_neg h1b_neg

end SolGammaHelpers

theorem solution {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4) (ht : 0 < t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) :=
  SolGammaHelpers.gaussian_sum_ge_le_quarter_aux hy hδ0 hδ_le ht
