-- Prove2me | solution 1 for RademacherGamma_gaussian_sum_ge_c1_box
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:57:07.380475+00:00
-- url     : https://prove2.me/submissions/028f0886-a94c-41b7-aa91-a7043eca8bad

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_RademacherGamma_p5_gauss_bounds

namespace SolGammaHelpers

open Real MeasureTheory Filter Set
open scoped Topology

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

private inductive BoxTree
  | leaf
  | splitY (m : ℕ) (l r : BoxTree)
  | splitT (m : ℕ) (l r : BoxTree)
  | splitX (m : ℕ) (l r : BoxTree)
  deriving DecidableEq

private def S_nat : ℕ := 1000000000

private def fmul (a b : ℕ) : ℕ := (a * b) / S_nat
private def cmul (a b : ℕ) : ℕ := (a * b + S_nat - 1) / S_nat
private def fdiv (a b : ℕ) : ℕ := (a * S_nat) / b
private def cdiv (a b : ℕ) : ℕ := (a * S_nat + b - 1) / b

private def expLb8Nat (x : ℕ) : ℕ :=
  let u := x / 8
  let u2 := fmul u u
  let u3 := fmul u2 u
  let p := S_nat + u + u2 / 2 + u3 / 6
  let p2 := fmul p p
  let p4 := fmul p2 p2
  fmul p4 p4

private def expNegLb32Nat (x : ℕ) : ℕ :=
  let u := (x + 31) / 32
  let u2_ub := cmul u u
  let u2_lb := fmul u u
  let u3_ub := cmul u2_ub u
  let pos := S_nat + u2_lb / 2
  let neg := u + (u3_ub + 5) / 6
  if pos ≤ neg then 0 else
    let val := pos - neg
    let v2 := fmul val val
    let v4 := fmul v2 v2
    let v8 := fmul v4 v4
    let v16 := fmul v8 v8
    fmul v16 v16

private def okC1Step (k : ℕ) (y0 y1 t0 t1 d0 d1 : ℕ) : ℕ :=
  let yk_lo := y0 + k * S_nat
  let xk := fmul (2 * fmul yk_lo d0) t0
  let sinh_lb := S_nat + fmul xk xk / 6
  let e_ub := 2 * k * y1 + k * k * S_nat + cmul d1 d1
  let e_t0 := cmul e_ub t0
  let e_t1 := cmul e_ub t1
  let u_min := min (fmul t0 (expNegLb32Nat e_t0)) (fmul t1 (expNegLb32Nat e_t1))
  fmul (2 * fmul yk_lo sinh_lb) u_min

private def okC1Nat (y0 y1 t0 t1 d0 d1 : ℕ) : Bool :=
  if 4 * y0 * t0 ≥ 3 * S_nat * S_nat then true
  else if y0 ≥ d1 ∧ 2 * (y0 - d1) * (y0 - d1) * t0 ≥ S_nat * S_nat * S_nat then true
  else
    let v_a := d0 * (2 * y0 - d0)
    let v_b := d1 * (2 * y0 - d1)
    let a0_lb := fmul (min v_a v_b / S_nat) t0
    let u0 := fmul y0 t0
    let du0_lb := fmul d1 u0
    let du0_ub := cmul d1 u0
    let du0_sq_ub := cmul du0_ub du0_ub
    let den0 := S_nat + 4 * du0_ub + 8 * du0_sq_ub
    let frac0 := fdiv (2 * fmul u0 (S_nat + 2 * du0_lb)) den0
    let s := fmul (S_nat + a0_lb) frac0 +
      okC1Step 1 y0 y1 t0 t1 d0 d1 + okC1Step 2 y0 y1 t0 t1 d0 d1 + okC1Step 3 y0 y1 t0 t1 d0 d1
    decide (s ≥ S_nat)


private def verifyTree (ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
    (t : BoxTree) (y0 y1 t0 t1 x0 x1 : ℕ) : Bool :=
  match t with
  | .leaf => decide (y0 ≤ y1 ∧ t0 ≤ t1 ∧ x0 < x1) && ok y0 y1 t0 t1 x0 x1
  | .splitY ym l r =>
      decide (y0 ≤ ym ∧ ym ≤ y1) && verifyTree ok l y0 ym t0 t1 x0 x1 && verifyTree ok r ym y1 t0 t1 x0 x1
  | .splitT tm l r =>
      decide (t0 ≤ tm ∧ tm ≤ t1) && verifyTree ok l y0 y1 t0 tm x0 x1 && verifyTree ok r y0 y1 tm t1 x0 x1
  | .splitX xm l r =>
      decide (x0 ≤ xm ∧ xm ≤ x1) && verifyTree ok l y0 y1 t0 t1 x0 xm && verifyTree ok r y0 y1 t0 t1 xm x1

private def c1aTree : BoxTree :=
  (.splitY 675000000 (.splitT 1850000000 (.splitY 462500000 (.splitT 1275000000 (.splitY 356250000 (.splitT 987500000 (.splitX 62500000 (.splitY 303125000 (.splitT 843750000 (.splitX 31250000 (.splitY 276562500 (.splitT 771875000 (.splitX 15625000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) .leaf) (.splitT 771875000 .leaf .leaf)) (.splitY 276562500 (.splitT 771875000 (.splitX 46875000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 46875000 .leaf .leaf)) (.splitT 771875000 .leaf .leaf))) (.splitX 31250000 (.splitY 276562500 (.splitT 915625000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 915625000 .leaf .leaf) .leaf))) (.splitT 843750000 (.splitX 31250000 (.splitT 771875000 .leaf .leaf) (.splitT 771875000 .leaf .leaf)) (.splitX 31250000 (.splitY 329687500 .leaf .leaf) (.splitY 329687500 .leaf .leaf)))) (.splitY 303125000 (.splitT 843750000 (.splitX 93750000 (.splitY 276562500 (.splitT 771875000 (.splitX 78125000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 78125000 .leaf .leaf)) (.splitT 771875000 .leaf .leaf)) (.splitY 276562500 (.splitT 771875000 (.splitX 109375000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 109375000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf))) (.splitT 771875000 .leaf .leaf))) (.splitX 93750000 (.splitY 276562500 (.splitT 915625000 .leaf .leaf) (.splitT 915625000 .leaf .leaf)) (.splitY 276562500 (.splitT 915625000 (.splitX 109375000 .leaf .leaf) .leaf) (.splitT 915625000 .leaf .leaf)))) (.splitT 843750000 (.splitX 93750000 (.splitT 771875000 .leaf .leaf) (.splitT 771875000 .leaf .leaf)) (.splitX 93750000 (.splitY 329687500 .leaf .leaf) (.splitY 329687500 .leaf .leaf))))) (.splitX 62500000 (.splitY 303125000 (.splitT 1131250000 (.splitX 31250000 (.splitY 276562500 (.splitT 1059375000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1059375000 .leaf .leaf) .leaf)) (.splitX 31250000 (.splitY 276562500 .leaf .leaf) (.splitY 276562500 .leaf .leaf))) (.splitT 1131250000 .leaf .leaf)) (.splitY 303125000 (.splitT 1131250000 (.splitX 93750000 (.splitY 276562500 (.splitT 1059375000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1059375000 .leaf .leaf) .leaf)) (.splitX 93750000 (.splitY 276562500 (.splitT 1203125000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1203125000 .leaf .leaf) .leaf))) (.splitT 1131250000 .leaf .leaf)))) (.splitT 987500000 (.splitX 62500000 (.splitT 843750000 (.splitY 409375000 .leaf .leaf) (.splitY 409375000 .leaf .leaf)) (.splitT 843750000 (.splitY 409375000 .leaf .leaf) (.splitY 409375000 .leaf .leaf))) (.splitX 62500000 (.splitY 409375000 .leaf .leaf) (.splitY 409375000 .leaf .leaf)))) (.splitY 356250000 (.splitX 62500000 (.splitT 1562500000 (.splitY 303125000 (.splitX 31250000 (.splitT 1418750000 (.splitY 276562500 .leaf .leaf) .leaf) (.splitT 1418750000 (.splitY 276562500 .leaf .leaf) .leaf)) .leaf) (.splitY 303125000 (.splitX 31250000 (.splitY 276562500 .leaf .leaf) (.splitY 276562500 .leaf .leaf)) .leaf)) (.splitT 1562500000 (.splitY 303125000 (.splitX 93750000 (.splitT 1418750000 (.splitY 276562500 .leaf .leaf) .leaf) (.splitT 1418750000 (.splitY 276562500 .leaf .leaf) (.splitY 276562500 .leaf .leaf))) .leaf) (.splitY 303125000 (.splitX 93750000 (.splitY 276562500 .leaf .leaf) (.splitY 276562500 .leaf .leaf)) .leaf))) (.splitX 62500000 (.splitT 1562500000 .leaf .leaf) (.splitT 1562500000 .leaf .leaf)))) (.splitT 1275000000 (.splitT 987500000 (.splitX 62500000 (.splitY 568750000 (.splitT 843750000 .leaf .leaf) .leaf) (.splitY 568750000 (.splitT 843750000 .leaf .leaf) .leaf)) (.splitX 62500000 .leaf .leaf)) .leaf)) (.splitY 462500000 (.splitY 356250000 (.splitT 2425000000 (.splitX 62500000 (.splitY 303125000 (.splitT 2137500000 .leaf .leaf) .leaf) (.splitY 303125000 (.splitT 2137500000 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)) (.splitT 1850000000 (.splitT 1275000000 (.splitT 987500000 (.splitY 887500000 .leaf .leaf) .leaf) .leaf) .leaf))

private def c1bTree : BoxTree :=
  (.splitY 675000000 (.splitT 1850000000 (.splitY 462500000 (.splitT 1275000000 (.splitY 356250000 (.splitT 987500000 (.splitX 187500000 (.splitY 303125000 (.splitT 843750000 (.splitX 156250000 (.splitY 276562500 (.splitT 771875000 (.splitX 140625000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 140625000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf))) (.splitT 771875000 .leaf .leaf)) (.splitY 276562500 (.splitT 771875000 (.splitX 171875000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 171875000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf))) (.splitT 771875000 .leaf .leaf))) (.splitX 156250000 (.splitY 276562500 (.splitT 915625000 (.splitX 140625000 .leaf (.splitY 263281250 .leaf .leaf)) .leaf) (.splitT 915625000 .leaf .leaf)) (.splitY 276562500 (.splitT 915625000 (.splitX 171875000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 171875000 .leaf (.splitY 263281250 .leaf .leaf))) (.splitT 915625000 .leaf .leaf)))) (.splitT 843750000 (.splitX 156250000 (.splitT 771875000 (.splitY 329687500 .leaf .leaf) .leaf) (.splitT 771875000 (.splitY 329687500 .leaf .leaf) .leaf)) (.splitX 156250000 (.splitY 329687500 .leaf .leaf) (.splitY 329687500 .leaf .leaf)))) (.splitY 303125000 (.splitT 843750000 (.splitX 218750000 (.splitY 276562500 (.splitT 771875000 (.splitX 203125000 (.splitY 263281250 (.splitT 735937500 .leaf .leaf) .leaf) (.splitY 263281250 (.splitT 735937500 .leaf .leaf) .leaf)) (.splitX 203125000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 (.splitT 807812500 .leaf .leaf) .leaf))) (.splitT 771875000 (.splitX 203125000 .leaf .leaf) .leaf)) (.splitY 276562500 (.splitT 771875000 (.splitX 234375000 (.splitY 263281250 (.splitT 735937500 .leaf .leaf) .leaf) (.splitY 263281250 (.splitT 735937500 .leaf .leaf) (.splitT 735937500 .leaf .leaf))) (.splitX 234375000 (.splitY 263281250 (.splitT 807812500 .leaf .leaf) .leaf) (.splitY 263281250 (.splitT 807812500 .leaf .leaf) .leaf))) (.splitT 771875000 (.splitX 234375000 (.splitT 735937500 .leaf .leaf) (.splitT 735937500 .leaf .leaf)) (.splitX 234375000 .leaf .leaf)))) (.splitX 218750000 (.splitY 276562500 (.splitT 915625000 (.splitX 203125000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 203125000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf))) (.splitT 915625000 .leaf .leaf)) (.splitY 276562500 (.splitT 915625000 (.splitX 234375000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 (.splitT 879687500 .leaf .leaf) .leaf)) (.splitX 234375000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf))) (.splitT 915625000 .leaf .leaf)))) (.splitT 843750000 (.splitX 218750000 (.splitT 771875000 (.splitY 329687500 .leaf .leaf) (.splitY 329687500 .leaf .leaf)) (.splitT 771875000 (.splitY 329687500 .leaf .leaf) (.splitY 329687500 .leaf .leaf))) (.splitX 218750000 (.splitY 329687500 .leaf .leaf) (.splitY 329687500 (.splitT 915625000 .leaf .leaf) .leaf))))) (.splitX 187500000 (.splitY 303125000 (.splitT 1131250000 (.splitX 156250000 (.splitY 276562500 (.splitT 1059375000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1059375000 (.splitX 171875000 .leaf .leaf) .leaf) (.splitT 1059375000 .leaf .leaf))) (.splitX 156250000 (.splitY 276562500 (.splitT 1203125000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1203125000 .leaf .leaf) .leaf))) (.splitT 1131250000 (.splitX 156250000 .leaf .leaf) .leaf)) (.splitY 303125000 (.splitT 1131250000 (.splitX 218750000 (.splitY 276562500 (.splitT 1059375000 (.splitX 203125000 .leaf (.splitY 263281250 .leaf .leaf)) (.splitX 203125000 .leaf .leaf)) (.splitT 1059375000 .leaf .leaf)) (.splitY 276562500 (.splitT 1059375000 (.splitX 234375000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) (.splitX 234375000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf))) (.splitT 1059375000 .leaf .leaf))) (.splitX 218750000 (.splitY 276562500 (.splitT 1203125000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1203125000 (.splitX 234375000 .leaf (.splitY 263281250 .leaf .leaf)) (.splitX 234375000 .leaf .leaf)) (.splitT 1203125000 .leaf .leaf)))) (.splitT 1131250000 (.splitX 218750000 (.splitY 329687500 .leaf .leaf) (.splitY 329687500 .leaf .leaf)) (.splitX 218750000 .leaf .leaf))))) (.splitT 987500000 (.splitX 187500000 (.splitT 843750000 (.splitY 409375000 (.splitX 156250000 .leaf .leaf) .leaf) (.splitY 409375000 .leaf .leaf)) (.splitT 843750000 (.splitY 409375000 (.splitX 218750000 (.splitT 771875000 .leaf .leaf) (.splitT 771875000 .leaf .leaf)) .leaf) (.splitY 409375000 .leaf .leaf))) (.splitX 187500000 (.splitY 409375000 (.splitT 1131250000 .leaf .leaf) .leaf) (.splitY 409375000 (.splitT 1131250000 .leaf .leaf) .leaf)))) (.splitY 356250000 (.splitX 187500000 (.splitT 1562500000 (.splitY 303125000 (.splitX 156250000 (.splitT 1418750000 (.splitY 276562500 .leaf .leaf) (.splitY 276562500 .leaf .leaf)) (.splitT 1418750000 (.splitY 276562500 (.splitX 171875000 .leaf (.splitT 1346875000 .leaf .leaf)) .leaf) (.splitY 276562500 .leaf .leaf))) (.splitX 156250000 .leaf .leaf)) (.splitY 303125000 (.splitX 156250000 (.splitY 276562500 (.splitT 1706250000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1706250000 .leaf .leaf) .leaf)) .leaf)) (.splitT 1562500000 (.splitY 303125000 (.splitX 218750000 (.splitT 1418750000 (.splitY 276562500 (.splitX 203125000 (.splitT 1346875000 .leaf .leaf) (.splitT 1346875000 .leaf .leaf)) .leaf) (.splitY 276562500 (.splitX 203125000 .leaf .leaf) .leaf)) (.splitT 1418750000 (.splitY 276562500 (.splitX 234375000 (.splitT 1346875000 .leaf .leaf) (.splitT 1346875000 .leaf .leaf)) .leaf) (.splitY 276562500 (.splitX 234375000 (.splitY 263281250 .leaf .leaf) (.splitY 263281250 .leaf .leaf)) .leaf))) (.splitX 218750000 (.splitT 1418750000 .leaf .leaf) (.splitT 1418750000 .leaf .leaf))) (.splitY 303125000 (.splitX 218750000 (.splitY 276562500 (.splitT 1706250000 .leaf .leaf) .leaf) (.splitY 276562500 (.splitT 1706250000 .leaf .leaf) .leaf)) .leaf))) (.splitX 187500000 (.splitT 1562500000 .leaf .leaf) (.splitT 1562500000 .leaf .leaf)))) (.splitT 1275000000 (.splitT 987500000 (.splitX 187500000 (.splitY 568750000 (.splitT 843750000 .leaf .leaf) .leaf) (.splitY 568750000 (.splitT 843750000 .leaf .leaf) .leaf)) (.splitX 187500000 .leaf (.splitY 568750000 .leaf .leaf))) .leaf)) (.splitY 462500000 (.splitY 356250000 (.splitT 2425000000 (.splitX 187500000 (.splitY 303125000 (.splitT 2137500000 .leaf .leaf) .leaf) (.splitY 303125000 (.splitT 2137500000 (.splitX 218750000 .leaf (.splitY 276562500 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf) .leaf)) (.splitT 1850000000 (.splitT 1275000000 (.splitT 987500000 (.splitY 887500000 .leaf .leaf) .leaf) .leaf) .leaf))


private lemma c1a_verified :
    verifyTree okC1Nat c1aTree (S_nat / 4) (11 * S_nat / 10) (7 * S_nat / 10) (3 * S_nat) 0 (S_nat / 8) = true := by
  decide

private lemma c1b_verified :
    verifyTree okC1Nat c1bTree (S_nat / 4) (11 * S_nat / 10) (7 * S_nat / 10) (3 * S_nat) (S_nat / 8) (S_nat / 4) = true := by
  decide


private lemma sinh_ge_poly3 {u : ℝ} (hu : 0 ≤ u) :
    u + u ^ 3 / 6 ≤ (Real.exp u - Real.exp (-u)) / 2 := by
  let f0 : ℝ → ℝ := fun t => (Real.exp t - Real.exp (-t)) / 2
  let f1 : ℝ → ℝ := fun t => (Real.exp t + Real.exp (-t)) / 2
  have hf0_der : ∀ t, HasDerivAt f0 (f1 t) t := by
    intro t
    have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_id t).neg.exp
    exact (((Real.hasDerivAt_exp t).fun_sub hneg).div_const 2).congr_deriv (by dsimp [f1]; ring)
  have hf1_der : ∀ t, HasDerivAt f1 (f0 t) t := by
    intro t
    have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_id t).neg.exp
    exact (((Real.hasDerivAt_exp t).fun_add hneg).div_const 2).congr_deriv (by dsimp [f0]; ring)
  have hf0_nn : ∀ t, 0 ≤ t → 0 ≤ f0 t := by
    intro t ht
    have hle : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    dsimp [f0]; linarith
  have hf1_ge : ∀ t, 0 ≤ t → 1 + t ^ 2 / 2 ≤ f1 t := by
    intro t ht
    have hf0_ge : ∀ y, 0 ≤ y → y ≤ f0 y := by
      intro y hy
      have hmono : MonotoneOn (fun z : ℝ => f0 z - z) (Set.Ici 0) :=
        monotoneOn_of_deriv_nonneg (convex_Ici 0)
          ((by dsimp [f0]; fun_prop : Continuous (fun z : ℝ => f0 z - z)).continuousOn)
          (fun z _ => ((hf0_der z).fun_sub (hasDerivAt_id z : HasDerivAt (fun x : ℝ => x) 1 z)).differentiableAt.differentiableWithinAt)
          fun z hz => by
            rw [interior_Ici] at hz
            have hid : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
            rw [((hf0_der z).fun_sub hid).deriv]
            have h2 : 2 ≤ Real.exp z + Real.exp (-z) := by
              have ha := Real.add_one_le_exp z
              have hb := Real.add_one_le_exp (-z)
              linarith
            dsimp [f1]; linarith
      have hm := hmono (by simp) hy hy
      dsimp [f0] at hm ⊢; norm_num at hm; linarith
    have hmono : MonotoneOn (fun z : ℝ => f1 z - (1 + z ^ 2 / 2)) (Set.Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0)
        ((by dsimp [f1]; fun_prop : Continuous (fun z : ℝ => f1 z - (1 + z ^ 2 / 2))).continuousOn)
        (fun z _ => ((hf1_der z).fun_sub ((hasDerivAt_const z (1 : ℝ)).fun_add
          (((hasDerivAt_pow 2 z).div_const 2).congr_deriv (by ring)))).differentiableAt.differentiableWithinAt)
        fun z hz => by
          rw [interior_Ici] at hz
          rw [((hf1_der z).fun_sub ((hasDerivAt_const z (1 : ℝ)).fun_add
            (((hasDerivAt_pow 2 z).div_const 2).congr_deriv (by ring)))).deriv]
          have := hf0_ge z hz.le; linarith
    have hm := hmono (by simp) ht ht
    dsimp [f1] at hm ⊢; norm_num at hm; linarith
  have hmono : MonotoneOn (fun z : ℝ => f0 z - (z + z ^ 3 / 6)) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((by dsimp [f0]; fun_prop : Continuous (fun z : ℝ => f0 z - (z + z ^ 3 / 6))).continuousOn)
      (fun z _ => by
        have hcub : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (z ^ 2 / 2) z :=
          ((hasDerivAt_pow 3 z).div_const 6).congr_deriv (by ring)
        have hid : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
        exact ((hf0_der z).fun_sub (hid.fun_add hcub)).differentiableAt.differentiableWithinAt)
      fun z hz => by
        rw [interior_Ici] at hz
        have hcub : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (z ^ 2 / 2) z :=
          ((hasDerivAt_pow 3 z).div_const 6).congr_deriv (by ring)
        have hid : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
        rw [((hf0_der z).fun_sub (hid.fun_add hcub)).deriv]
        have := hf1_ge z hz.le; linarith
  have hm := hmono (by simp) hu hu
  dsimp [f0] at hm ⊢; norm_num at hm; linarith

private lemma fmul_le (a b : ℕ) :
    ((fmul a b : ℕ) : ℝ) / S_nat ≤ ((a : ℝ) / S_nat) * ((b : ℝ) / S_nat) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hnat : fmul a b * S_nat ≤ a * b := Nat.div_mul_le_self _ _
  have hr : ((fmul a b : ℕ) : ℝ) * S_nat ≤ (a : ℝ) * b := by exact_mod_cast hnat
  rw [div_mul_div_comm, div_le_div_iff₀ hS (mul_pos hS hS)]
  nlinarith only [hr]

private lemma le_cmul (a b : ℕ) :
    ((a : ℝ) / S_nat) * ((b : ℝ) / S_nat) ≤ ((cmul a b : ℕ) : ℝ) / S_nat := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hnat : a * b ≤ cmul a b * S_nat := by
    have hlt := Nat.lt_div_mul_add (a := a * b + S_nat - 1) (by norm_num [S_nat] : 0 < S_nat)
    dsimp [cmul]; omega
  have hr : (a : ℝ) * b ≤ ((cmul a b : ℕ) : ℝ) * S_nat := by exact_mod_cast hnat
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hS hS) hS]
  nlinarith only [hr]

private lemma fdiv_le (a b : ℕ) (hb : 0 < b) :
    ((fdiv a b : ℕ) : ℝ) / S_nat ≤ (a : ℝ) / b := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hnat : fdiv a b * b ≤ a * S_nat := Nat.div_mul_le_self _ _
  have hr : ((fdiv a b : ℕ) : ℝ) * b ≤ (a : ℝ) * S_nat := by exact_mod_cast hnat
  rw [div_le_div_iff₀ hS hb']
  exact hr

private lemma le_cdiv (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / b ≤ ((cdiv a b : ℕ) : ℝ) / S_nat := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hnat : a * S_nat ≤ cdiv a b * b := by
    have hlt := Nat.lt_div_mul_add (a := a * S_nat + b - 1) hb
    dsimp [cdiv]; omega
  have hr : (a : ℝ) * S_nat ≤ ((cdiv a b : ℕ) : ℝ) * b := by exact_mod_cast hnat
  rw [div_le_div_iff₀ hb' hS]
  exact hr

private lemma fmul_ge_S_of_ge_S {a b : ℕ} (ha : S_nat ≤ a) (hb : S_nat ≤ b) : S_nat ≤ fmul a b := by
  dsimp [fmul]
  rw [Nat.le_div_iff_mul_le (by norm_num [S_nat] : 0 < S_nat)]
  exact Nat.mul_le_mul ha hb

private lemma expLb8Nat_ge_S (x : ℕ) : S_nat ≤ expLb8Nat x := by
  dsimp [expLb8Nat]
  have hp : S_nat ≤ S_nat + x / 8 + fmul (x / 8) (x / 8) / 2 + fmul (fmul (x / 8) (x / 8)) (x / 8) / 6 := by
    omega
  have hp2 := fmul_ge_S_of_ge_S hp hp
  have hp4 := fmul_ge_S_of_ge_S hp2 hp2
  exact fmul_ge_S_of_ge_S hp4 hp4

private lemma expLb8Nat_le_exp (x : ℕ) :
    ((expLb8Nat x : ℕ) : ℝ) / S_nat ≤ Real.exp ((x : ℝ) / S_nat) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  set u := x / 8
  set u2 := fmul u u
  set u3 := fmul u2 u
  set p := S_nat + u + u2 / 2 + u3 / 6
  set p2 := fmul p p
  set p4 := fmul p2 p2
  have hu_nat : 8 * u ≤ x := Nat.mul_div_le x 8
  have hu2 : (u2 : ℝ) / S_nat ≤ ((u : ℝ) / S_nat) ^ 2 := by
    have := fmul_le u u; linarith [sq ((u : ℝ) / S_nat)]
  have hu3 : (u3 : ℝ) / S_nat ≤ ((u : ℝ) / S_nat) ^ 3 := by
    have h1 := fmul_le u2 u
    have h2 : ((u2 : ℝ) / S_nat) * ((u : ℝ) / S_nat) ≤ ((u : ℝ) / S_nat) ^ 2 * ((u : ℝ) / S_nat) :=
      mul_le_mul_of_nonneg_right hu2 (div_nonneg (Nat.cast_nonneg _) hS.le)
    linarith [show ((u : ℝ) / S_nat) ^ 2 * ((u : ℝ) / S_nat) = ((u : ℝ) / S_nat) ^ 3 by ring]
  have hd2 : ((u2 / 2 : ℕ) : ℝ) ≤ (u2 : ℝ) / 2 := by
    have : (u2 / 2 : ℕ) * 2 ≤ u2 := Nat.div_mul_le_self _ _
    have : ((u2 / 2 : ℕ) : ℝ) * 2 ≤ u2 := by exact_mod_cast this
    linarith
  have hd6 : ((u3 / 6 : ℕ) : ℝ) ≤ (u3 : ℝ) / 6 := by
    have : (u3 / 6 : ℕ) * 6 ≤ u3 := Nat.div_mul_le_self _ _
    have : ((u3 / 6 : ℕ) : ℝ) * 6 ≤ u3 := by exact_mod_cast this
    linarith
  have hp_le : (p : ℝ) / S_nat ≤ Real.exp ((u : ℝ) / S_nat) := by
    have hsum : (p : ℝ) / S_nat ≤ 1 + (u : ℝ) / S_nat + ((u : ℝ) / S_nat) ^ 2 / 2 + ((u : ℝ) / S_nat) ^ 3 / 6 := by
      have hp_eq : (p : ℝ) = S_nat + u + ((u2 / 2 : ℕ) : ℝ) + ((u3 / 6 : ℕ) : ℝ) := by
        dsimp [p]; push_cast; ring
      rw [hp_eq]
      have : (S_nat + (u : ℝ) + ((u2 / 2 : ℕ) : ℝ) + ((u3 / 6 : ℕ) : ℝ)) / S_nat =
          1 + (u : ℝ) / S_nat + ((u2 / 2 : ℕ) : ℝ) / S_nat + ((u3 / 6 : ℕ) : ℝ) / S_nat := by
        field_simp
      rw [this]
      have d2' : ((u2 / 2 : ℕ) : ℝ) / S_nat ≤ ((u : ℝ) / S_nat) ^ 2 / 2 := by
        have h1 := div_le_div_of_nonneg_right hd2 hS.le
        have h2 := div_le_div_of_nonneg_right hu2 (by norm_num : (0 : ℝ) ≤ 2)
        have h3 : ((u2 : ℝ) / 2) / S_nat = ((u2 : ℝ) / S_nat) / 2 := by ring
        linarith
      have d6' : ((u3 / 6 : ℕ) : ℝ) / S_nat ≤ ((u : ℝ) / S_nat) ^ 3 / 6 := by
        have h1 := div_le_div_of_nonneg_right hd6 hS.le
        have h2 := div_le_div_of_nonneg_right hu3 (by norm_num : (0 : ℝ) ≤ 6)
        have h3 : ((u3 : ℝ) / 6) / S_nat = ((u3 : ℝ) / S_nat) / 6 := by ring
        linarith
      linarith
    exact le_trans hsum (exp_ge_poly3 (div_nonneg (Nat.cast_nonneg _) hS.le))
  have hp2_le : (p2 : ℝ) / S_nat ≤ (Real.exp ((u : ℝ) / S_nat)) ^ 2 := by
    have h1 := fmul_le p p
    have h2 : ((p : ℝ) / S_nat) * ((p : ℝ) / S_nat) ≤ Real.exp ((u : ℝ) / S_nat) * Real.exp ((u : ℝ) / S_nat) :=
      mul_le_mul hp_le hp_le (div_nonneg (Nat.cast_nonneg _) hS.le) (Real.exp_pos _).le
    linarith [sq (Real.exp ((u : ℝ) / S_nat))]
  have hp4_le : (p4 : ℝ) / S_nat ≤ (Real.exp ((u : ℝ) / S_nat)) ^ 4 := by
    have h1 := fmul_le p2 p2
    have h2 : ((p2 : ℝ) / S_nat) * ((p2 : ℝ) / S_nat) ≤ (Real.exp ((u : ℝ) / S_nat)) ^ 2 * (Real.exp ((u : ℝ) / S_nat)) ^ 2 :=
      mul_le_mul hp2_le hp2_le (div_nonneg (Nat.cast_nonneg _) hS.le) (by positivity)
    linarith [show ((Real.exp ((u : ℝ) / S_nat)) ^ 2) * ((Real.exp ((u : ℝ) / S_nat)) ^ 2) =
      (Real.exp ((u : ℝ) / S_nat)) ^ 4 by ring]
  have hp8_le : ((fmul p4 p4 : ℕ) : ℝ) / S_nat ≤ (Real.exp ((u : ℝ) / S_nat)) ^ 8 := by
    have h1 := fmul_le p4 p4
    have h2 : ((p4 : ℝ) / S_nat) * ((p4 : ℝ) / S_nat) ≤ (Real.exp ((u : ℝ) / S_nat)) ^ 4 * (Real.exp ((u : ℝ) / S_nat)) ^ 4 :=
      mul_le_mul hp4_le hp4_le (div_nonneg (Nat.cast_nonneg _) hS.le) (by positivity)
    linarith [show ((Real.exp ((u : ℝ) / S_nat)) ^ 4) * ((Real.exp ((u : ℝ) / S_nat)) ^ 4) =
      (Real.exp ((u : ℝ) / S_nat)) ^ 8 by ring]
  have hexp8 : (Real.exp ((u : ℝ) / S_nat)) ^ 8 = Real.exp (8 * ((u : ℝ) / S_nat)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hu_real : 8 * ((u : ℝ) / S_nat) ≤ (x : ℝ) / S_nat := by
    have h8 : (8 * (u : ℝ)) ≤ x := by exact_mod_cast hu_nat
    have hdiv := div_le_div_of_nonneg_right h8 hS.le
    rw [mul_div_assoc']
    exact hdiv
  exact le_trans hp8_le (by rw [hexp8]; exact Real.exp_le_exp.mpr hu_real)

private lemma expNegLb32Nat_le_exp (x : ℕ) :
    ((expNegLb32Nat x : ℕ) : ℝ) / S_nat ≤ Real.exp (-((x : ℝ) / S_nat)) := by
  dsimp [expNegLb32Nat]
  split_ifs with hpn
  · simp only [Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le
  · have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
    set u := (x + 31) / 32
    set u2_ub := cmul u u
    set u2_lb := fmul u u
    set u3_ub := cmul u2_ub u
    set pos := S_nat + u2_lb / 2
    set neg := u + (u3_ub + 5) / 6
    set val := pos - neg
    have hle_pn : neg ≤ pos := Nat.le_of_not_ge hpn
    have hval_cast : (val : ℝ) = (pos : ℝ) - (neg : ℝ) := by
      dsimp [val]; exact Nat.cast_sub hle_pn
    have hu2_lb : (u2_lb : ℝ) / S_nat ≤ ((u : ℝ) / S_nat) ^ 2 := by
      have := fmul_le u u; linarith [sq ((u : ℝ) / S_nat)]
    have hu2_ub : ((u : ℝ) / S_nat) ^ 2 ≤ (u2_ub : ℝ) / S_nat := by
      have := le_cmul u u; linarith [sq ((u : ℝ) / S_nat)]
    have hu3_ub : ((u : ℝ) / S_nat) ^ 3 ≤ (u3_ub : ℝ) / S_nat := by
      have h1 := le_cmul u2_ub u
      have h2 : ((u : ℝ) / S_nat) ^ 2 * ((u : ℝ) / S_nat) ≤ ((u2_ub : ℝ) / S_nat) * ((u : ℝ) / S_nat) :=
        mul_le_mul_of_nonneg_right hu2_ub (div_nonneg (Nat.cast_nonneg _) hS.le)
      linarith [show ((u : ℝ) / S_nat) ^ 2 * ((u : ℝ) / S_nat) = ((u : ℝ) / S_nat) ^ 3 by ring]
    have hd2 : ((u2_lb / 2 : ℕ) : ℝ) ≤ (u2_lb : ℝ) / 2 := by
      have : (u2_lb / 2 : ℕ) * 2 ≤ u2_lb := Nat.div_mul_le_self _ _
      have : ((u2_lb / 2 : ℕ) : ℝ) * 2 ≤ u2_lb := by exact_mod_cast this
      linarith
    have hd6 : (u3_ub : ℝ) / 6 ≤ (((u3_ub + 5) / 6 : ℕ) : ℝ) := by
      have hlt : u3_ub ≤ ((u3_ub + 5) / 6) * 6 := by
        have := Nat.lt_div_mul_add (a := u3_ub + 5) (by norm_num : 0 < 6)
        omega
      have : (u3_ub : ℝ) ≤ (((u3_ub + 5) / 6 : ℕ) : ℝ) * 6 := by exact_mod_cast hlt
      linarith
    have hval_le : (val : ℝ) / S_nat ≤ Real.exp (-((u : ℝ) / S_nat)) := by
      have h1 : (val : ℝ) / S_nat ≤ 1 - (u : ℝ) / S_nat + ((u : ℝ) / S_nat) ^ 2 / 2 - ((u : ℝ) / S_nat) ^ 3 / 6 := by
        rw [hval_cast]
        have hpos_r : (pos : ℝ) = S_nat + ((u2_lb / 2 : ℕ) : ℝ) := by dsimp [pos]; push_cast; ring
        have hneg_r : (neg : ℝ) = u + (((u3_ub + 5) / 6 : ℕ) : ℝ) := by dsimp [neg]; push_cast; ring
        rw [hpos_r, hneg_r]
        have hdiv_eq : (S_nat + ((u2_lb / 2 : ℕ) : ℝ) - (u + (((u3_ub + 5) / 6 : ℕ) : ℝ))) / S_nat =
            1 - (u : ℝ) / S_nat + ((u2_lb / 2 : ℕ) : ℝ) / S_nat - (((u3_ub + 5) / 6 : ℕ) : ℝ) / S_nat := by
          field_simp; ring
        rw [hdiv_eq]
        have d2' : ((u2_lb / 2 : ℕ) : ℝ) / S_nat ≤ ((u : ℝ) / S_nat) ^ 2 / 2 := by
          have h1' := div_le_div_of_nonneg_right hd2 hS.le
          have h2' := div_le_div_of_nonneg_right hu2_lb (by norm_num : (0 : ℝ) ≤ 2)
          have h3' : ((u2_lb : ℝ) / 2) / S_nat = ((u2_lb : ℝ) / S_nat) / 2 := by ring
          linarith
        have d6' : ((u : ℝ) / S_nat) ^ 3 / 6 ≤ (((u3_ub + 5) / 6 : ℕ) : ℝ) / S_nat := by
          have h1' := div_le_div_of_nonneg_right hd6 hS.le
          have h2' := div_le_div_of_nonneg_right hu3_ub (by norm_num : (0 : ℝ) ≤ 6)
          have h3' : ((u3_ub : ℝ) / 6) / S_nat = ((u3_ub : ℝ) / S_nat) / 6 := by ring
          linarith
        linarith
      exact le_trans h1 (exp_neg_ge_poly3 (div_nonneg (Nat.cast_nonneg _) hS.le))
    have step_sq : ∀ {a : ℕ} {B : ℝ}, 0 ≤ B → (a : ℝ) / S_nat ≤ B → ((fmul a a : ℕ) : ℝ) / S_nat ≤ B ^ 2 := by
      intro a B _ ha
      have h1 := fmul_le a a
      have h2 := mul_le_mul ha ha (div_nonneg (Nat.cast_nonneg _) hS.le) (le_trans (div_nonneg (Nat.cast_nonneg _) hS.le) ha)
      linarith [sq B]
    have hv2 := step_sq (Real.exp_pos _).le hval_le
    have hv4 := step_sq (by positivity) hv2
    have hv8 := step_sq (by positivity) hv4
    have hv16 := step_sq (by positivity) hv8
    have hv32 := step_sq (by positivity) hv16
    have hexp32 : ((((Real.exp (-((u : ℝ) / S_nat)) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 =
        Real.exp (-32 * ((u : ℝ) / S_nat)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      ring_nf
    have hx_le : x ≤ 32 * u := by
      have hlt := Nat.lt_div_mul_add (a := x + 31) (by norm_num : 0 < 32)
      dsimp [u]; omega
    have hu_real : -32 * ((u : ℝ) / S_nat) ≤ -((x : ℝ) / S_nat) := by
      have hx' : (x : ℝ) ≤ 32 * u := by exact_mod_cast hx_le
      have hdiv := div_le_div_of_nonneg_right hx' hS.le
      rw [mul_div_assoc] at hdiv
      linarith [hdiv]
    exact le_trans hv32 (by rw [hexp32]; exact Real.exp_le_exp.mpr hu_real)

private lemma t_mul_exp_neg_ge_min {E t0 t1 t : ℝ} (hE : 0 ≤ E) (_ht0 : 0 ≤ t0)
    (h0 : t0 ≤ t) (h1 : t ≤ t1) :
    min (t0 * Real.exp (-E * t0)) (t1 * Real.exp (-E * t1)) ≤ t * Real.exp (-E * t) := by
  let f : ℝ → ℝ := fun u => u * Real.exp (-E * u)
  have hf_der : ∀ u, HasDerivAt f ((1 - E * u) * Real.exp (-E * u)) u := by
    intro u
    have h1' : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
    have h2' : HasDerivAt (fun x : ℝ => Real.exp (-E * x)) (-E * Real.exp (-E * u)) u := by
      have hl : HasDerivAt (fun x : ℝ => -E * x) (-E) u := by
        simpa using (hasDerivAt_id u).const_mul (-E)
      convert hl.exp using 1; ring
    exact (h1'.fun_mul h2').congr_deriv (by ring)
  by_cases hEt : E * t ≤ 1
  · have hmono : MonotoneOn f (Set.Icc t0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact (by dsimp [f]; fun_prop : Continuous f).continuousOn
      · exact fun u _ => (hf_der u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hf_der u).deriv]
        have : E * u ≤ 1 := by nlinarith only [hE, hu.2, hEt]
        exact mul_nonneg (by linarith) (Real.exp_pos _).le
    exact le_trans (min_le_left _ _) (hmono ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0)
  · have hEt_ge : 1 ≤ E * t := le_of_not_ge hEt
    have hant : AntitoneOn f (Set.Icc t t1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact (by dsimp [f]; fun_prop : Continuous f).continuousOn
      · exact fun u _ => (hf_der u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hf_der u).deriv]
        have : 1 ≤ E * u := by nlinarith only [hE, hu.1, hEt_ge]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    exact le_trans (min_le_right _ _) (hant ⟨le_rfl, h1⟩ ⟨h1, le_rfl⟩ h1)

private lemma t_mul_exp_neg_le_unimax {E t0 t1 t e_lb : ℝ} (hE : 0 < E) (_ht0 : 0 ≤ t0)
    (h0 : t0 ≤ t) (h1 : t ≤ t1) (he : 0 < e_lb) (hel : e_lb ≤ Real.exp 1) :
    t * Real.exp (-E * t) ≤
      if 1 ≤ E * t0 then t0 * Real.exp (-E * t0)
      else if E * t1 ≤ 1 then t1 * Real.exp (-E * t1)
      else 1 / (E * e_lb) := by
  let f : ℝ → ℝ := fun u => u * Real.exp (-E * u)
  have hf_der : ∀ u, HasDerivAt f ((1 - E * u) * Real.exp (-E * u)) u := by
    intro u
    have h1' : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
    have h2' : HasDerivAt (fun x : ℝ => Real.exp (-E * x)) (-E * Real.exp (-E * u)) u := by
      have hl : HasDerivAt (fun x : ℝ => -E * x) (-E) u := by
        simpa using (hasDerivAt_id u).const_mul (-E)
      convert hl.exp using 1; ring
    exact (h1'.fun_mul h2').congr_deriv (by ring)
  split_ifs with hlo hhi
  · have hant : AntitoneOn f (Set.Icc t0 t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact (by dsimp [f]; fun_prop : Continuous f).continuousOn
      · exact fun u _ => (hf_der u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hf_der u).deriv]
        have : 1 ≤ E * u := by nlinarith only [hE, hu.1, hlo]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    exact hant ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  · have hmono : MonotoneOn f (Set.Icc t t1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact (by dsimp [f]; fun_prop : Continuous f).continuousOn
      · exact fun u _ => (hf_der u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hf_der u).deriv]
        have : E * u ≤ 1 := by nlinarith only [hE, hu.2, hhi]
        exact mul_nonneg (by linarith) (Real.exp_pos _).le
    exact hmono ⟨le_rfl, h1⟩ ⟨h1, le_rfl⟩ h1
  · have hadd := Real.add_one_le_exp (E * t - 1)
    have hexp_split : Real.exp (E * t - 1) = Real.exp (E * t) * Real.exp (-1) := by
      rw [sub_eq_add_neg, Real.exp_add]
    have hmul_e : E * t * Real.exp (-E * t) ≤ Real.exp (-1) := by
      have hsub : E * t ≤ Real.exp (E * t - 1) := by linarith
      rw [hexp_split] at hsub
      have hmul := mul_le_mul_of_nonneg_right hsub (Real.exp_pos (-E * t)).le
      have hc : Real.exp (E * t) * Real.exp (-1) * Real.exp (-E * t) = Real.exp (-1) := by
        calc Real.exp (E * t) * Real.exp (-1) * Real.exp (-E * t)
            = (Real.exp (E * t) * Real.exp (-E * t)) * Real.exp (-1) := by ring
          _ = Real.exp (E * t + (-E * t)) * Real.exp (-1) := by rw [← Real.exp_add]
          _ = Real.exp (-1) := by simp
      linarith [hmul, hc]
    have hdiv_e : t * Real.exp (-E * t) ≤ 1 / (E * Real.exp 1) := by
      rw [le_div_iff₀ (mul_pos hE (Real.exp_pos 1))]
      have h1 : E * t * Real.exp (-E * t) * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
        mul_le_mul_of_nonneg_right hmul_e (Real.exp_pos 1).le
      have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      linarith [show t * Real.exp (-E * t) * (E * Real.exp 1) = E * t * Real.exp (-E * t) * Real.exp 1 by ring]
    have hcmp : 1 / (E * Real.exp 1) ≤ 1 / (E * e_lb) := by
      rw [one_div, one_div]
      exact inv_anti₀ (mul_pos hE he) (mul_le_mul_of_nonneg_left hel hE.le)
    exact le_trans hdiv_e hcmp

private lemma t_mul_exp_neg_le_peak {E t e_lb : ℝ} (hE : 0 < E) (he : 0 < e_lb) (hel : e_lb ≤ Real.exp 1) :
    t * Real.exp (-E * t) ≤ 1 / (E * e_lb) := by
  have hadd := Real.add_one_le_exp (E * t - 1)
  have hexp_split : Real.exp (E * t - 1) = Real.exp (E * t) * Real.exp (-1) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hmul_e : E * t * Real.exp (-E * t) ≤ Real.exp (-1) := by
    have hsub : E * t ≤ Real.exp (E * t - 1) := by linarith
    rw [hexp_split] at hsub
    have hmul := mul_le_mul_of_nonneg_right hsub (Real.exp_pos (-E * t)).le
    have hc : Real.exp (E * t) * Real.exp (-1) * Real.exp (-E * t) = Real.exp (-1) := by
      calc Real.exp (E * t) * Real.exp (-1) * Real.exp (-E * t)
          = (Real.exp (E * t) * Real.exp (-E * t)) * Real.exp (-1) := by ring
        _ = Real.exp (E * t + (-E * t)) * Real.exp (-1) := by rw [← Real.exp_add]
        _ = Real.exp (-1) := by simp
    linarith [hmul, hc]
  have hdiv_e : t * Real.exp (-E * t) ≤ 1 / (E * Real.exp 1) := by
    rw [le_div_iff₀ (mul_pos hE (Real.exp_pos 1))]
    have h1 : E * t * Real.exp (-E * t) * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
      mul_le_mul_of_nonneg_right hmul_e (Real.exp_pos 1).le
    have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linarith [show t * Real.exp (-E * t) * (E * Real.exp 1) = E * t * Real.exp (-E * t) * Real.exp 1 by ring]
  have hcmp : 1 / (E * Real.exp 1) ≤ 1 / (E * e_lb) := by
    rw [one_div, one_div]
    exact inv_anti₀ (mul_pos hE he) (mul_le_mul_of_nonneg_left hel hE.le)
  exact le_trans hdiv_e hcmp

private lemma h_gauss_nonneg {w δ t : ℝ} (hw : δ ≤ w) (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    0 ≤ Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t) := by
  have hsq : (w - δ) ^ 2 ≤ (w + δ) ^ 2 := by nlinarith only [hw, hδ]
  have hexp : Real.exp (-(w + δ) ^ 2 * t) ≤ Real.exp (-(w - δ) ^ 2 * t) :=
    Real.exp_le_exp.mpr (by nlinarith only [hsq, ht])
  linarith


private lemma okC1Step_sound {k y0 y1 t0 t1 d0 d1 : ℕ}
    (_hy01 : y0 ≤ y1) (_ht01 : t0 ≤ t1) (_hd01 : d0 ≤ d1)
    {y t δ : ℝ} (hy0 : (y0 : ℝ) / S_nat ≤ y) (hy1 : y ≤ (y1 : ℝ) / S_nat)
    (ht0 : (t0 : ℝ) / S_nat ≤ t) (ht1 : t ≤ (t1 : ℝ) / S_nat)
    (hd0 : (d0 : ℝ) / S_nat ≤ δ) (hd1 : δ ≤ (d1 : ℝ) / S_nat) (hδ : 0 < δ) :
    ((okC1Step k y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) ≤
      Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hy0_nn : 0 ≤ (y0 : ℝ) / S_nat := by positivity
  have ht0_nn : 0 ≤ (t0 : ℝ) / S_nat := by positivity
  have hd0_nn : 0 ≤ (d0 : ℝ) / S_nat := by positivity
  have hy_nn : 0 ≤ y := le_trans hy0_nn hy0
  have ht_nn : 0 ≤ t := le_trans ht0_nn ht0
  set yk_lo := y0 + k * S_nat
  set xk := fmul (2 * fmul yk_lo d0) t0
  set sinh_lb := S_nat + fmul xk xk / 6
  set e_ub := 2 * k * y1 + k * k * S_nat + cmul d1 d1
  set e_t0 := cmul e_ub t0
  set e_t1 := cmul e_ub t1
  set u_min := min (fmul t0 (expNegLb32Nat e_t0)) (fmul t1 (expNegLb32Nat e_t1))
  have hyk_le : (yk_lo : ℝ) / S_nat ≤ y + k := by
    have heq : (yk_lo : ℝ) = (y0 : ℝ) + k * S_nat := by dsimp [yk_lo]; push_cast; ring
    rw [heq, add_div, mul_div_cancel_right₀ _ hS.ne']
    linarith only [hy0]
  have hyk_nn : 0 ≤ (yk_lo : ℝ) / S_nat := by positivity
  have hxk_le : (xk : ℝ) / S_nat ≤ 2 * (y + k) * δ * t := by
    have h1 := fmul_le (2 * fmul yk_lo d0) t0
    have h2 : ((2 * fmul yk_lo d0 : ℕ) : ℝ) / S_nat = 2 * (((fmul yk_lo d0 : ℕ) : ℝ) / S_nat) := by
      push_cast; ring
    have h3 := fmul_le yk_lo d0
    have h4 : 2 * (((fmul yk_lo d0 : ℕ) : ℝ) / S_nat) ≤ 2 * ((y + k) * δ) := by
      have hm := mul_le_mul hyk_le hd0 hd0_nn (by linarith only [hy_nn])
      linarith only [h3, mul_le_mul_of_nonneg_left hm zero_le_two]
    have hm2 := mul_le_mul h4 ht0 ht0_nn (mul_nonneg (by norm_num) (mul_nonneg (by linarith only [hy_nn]) hδ.le))
    rw [h2] at h1
    linarith only [h1, hm2, show 2 * ((y + k) * δ) * t = 2 * (y + k) * δ * t by ring]
  have hxtrue_nn : 0 ≤ 2 * (y + k) * δ * t := by positivity
  have hsinh_exp : Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t) =
      2 * Real.exp (-((y + k) ^ 2 + δ ^ 2) * t) *
        ((Real.exp (2 * (y + k) * δ * t) - Real.exp (-(2 * (y + k) * δ * t))) / 2) := by
    have harg1 : -((y + k) ^ 2 + δ ^ 2) * t + 2 * (y + k) * δ * t = -(y + k - δ) ^ 2 * t := by ring
    have harg2 : -((y + k) ^ 2 + δ ^ 2) * t + -(2 * (y + k) * δ * t) = -(y + k + δ) ^ 2 * t := by ring
    calc Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)
        = Real.exp (-((y + k) ^ 2 + δ ^ 2) * t) * Real.exp (2 * (y + k) * δ * t) -
            Real.exp (-((y + k) ^ 2 + δ ^ 2) * t) * Real.exp (-(2 * (y + k) * δ * t)) := by
            rw [← Real.exp_add, ← Real.exp_add, harg1, harg2]
      _ = 2 * Real.exp (-((y + k) ^ 2 + δ ^ 2) * t) *
            ((Real.exp (2 * (y + k) * δ * t) - Real.exp (-(2 * (y + k) * δ * t))) / 2) := by ring
  have hsinh_lb_le : ((sinh_lb : ℕ) : ℝ) / S_nat ≤ 1 + ((xk : ℝ) / S_nat) ^ 2 / 6 := by
    have h1 := fmul_le xk xk
    have h2 : ((fmul xk xk / 6 : ℕ) : ℝ) ≤ (fmul xk xk : ℝ) / 6 := by
      have hdiv_nat : (fmul xk xk / 6 : ℕ) * 6 ≤ fmul xk xk := Nat.div_mul_le_self _ _
      have hdiv_r : ((fmul xk xk / 6 : ℕ) : ℝ) * 6 ≤ fmul xk xk := by exact_mod_cast hdiv_nat
      linarith only [hdiv_r]
    have hdiv : ((fmul xk xk / 6 : ℕ) : ℝ) / S_nat ≤ ((xk : ℝ) / S_nat) ^ 2 / 6 := by
      have ha := div_le_div_of_nonneg_right h2 hS.le
      have hb := div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 6)
      rw [div_div, mul_comm (S_nat : ℝ) 6, ← div_div, ← sq] at hb
      exact le_trans ha hb
    have hcast : ((sinh_lb : ℕ) : ℝ) / S_nat = 1 + ((fmul xk xk / 6 : ℕ) : ℝ) / S_nat := by
      dsimp [sinh_lb]; push_cast; field_simp
    rw [hcast]; exact add_le_add_right hdiv 1
  have hsinh_bound : 2 * δ * t * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) ≤
      (Real.exp (2 * (y + k) * δ * t) - Real.exp (-(2 * (y + k) * δ * t))) / 2 := by
    have hs3 := sinh_ge_poly3 hxtrue_nn
    have hxk2 : ((xk : ℝ) / S_nat) ^ 2 ≤ (2 * (y + k) * δ * t) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hS.le) hxk_le 2
    have hterm : 2 * (y + k) * δ * t * ((sinh_lb : ℝ) / S_nat) ≤
        2 * (y + k) * δ * t + (2 * (y + k) * δ * t) ^ 3 / 6 := by
      have h1' : (sinh_lb : ℝ) / S_nat ≤ 1 + (2 * (y + k) * δ * t) ^ 2 / 6 :=
        le_trans hsinh_lb_le (by linarith only [hxk2])
      have hm := mul_le_mul_of_nonneg_left h1' hxtrue_nn
      linarith only [hm, show 2 * (y + k) * δ * t * (1 + (2 * (y + k) * δ * t) ^ 2 / 6) =
        2 * (y + k) * δ * t + (2 * (y + k) * δ * t) ^ 3 / 6 by ring]
    have hmono_y : 2 * δ * t * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) ≤
        2 * (y + k) * δ * t * ((sinh_lb : ℝ) / S_nat) := by
      have hnn : 0 ≤ 2 * δ * t * ((sinh_lb : ℝ) / S_nat) :=
        mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg _) hS.le)
      have hm := mul_le_mul_of_nonneg_right hyk_le hnn
      linarith only [hm]
    linarith only [hs3, hterm, hmono_y]
  have he_ub_le : 2 * k * y + k ^ 2 + δ ^ 2 ≤ (e_ub : ℝ) / S_nat := by
    have hd1_sq : δ ^ 2 ≤ (cmul d1 d1 : ℝ) / S_nat := by
      have hcm := le_cmul d1 d1
      have hsq : δ ^ 2 ≤ ((d1 : ℝ) / S_nat) ^ 2 := pow_le_pow_left₀ hδ.le hd1 2
      have hsq2 := sq ((d1 : ℝ) / S_nat)
      linarith only [hcm, hsq, hsq2]
    have hy_le : y ≤ (y1 : ℝ) / S_nat := hy1
    have hcast : (e_ub : ℝ) / S_nat = 2 * k * ((y1 : ℝ) / S_nat) + (k : ℝ) ^ 2 + (cmul d1 d1 : ℝ) / S_nat := by
      dsimp [e_ub]; push_cast; field_simp
    rw [hcast]
    exact add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left hy_le (by positivity)) _) hd1_sq
  have he_ub_nn : 0 ≤ (e_ub : ℝ) / S_nat := by positivity
  have ht_exp : (u_min : ℝ) / S_nat ≤ t * Real.exp (-((e_ub : ℝ) / S_nat) * t) := by
    have het0_le : ((e_ub : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) ≤ (e_t0 : ℝ) / S_nat := le_cmul e_ub t0
    have het1_le : ((e_ub : ℝ) / S_nat) * ((t1 : ℝ) / S_nat) ≤ (e_t1 : ℝ) / S_nat := le_cmul e_ub t1
    have hu0 : ((fmul t0 (expNegLb32Nat e_t0) : ℕ) : ℝ) / S_nat ≤
        ((t0 : ℝ) / S_nat) * Real.exp (-((e_ub : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) := by
      have h1 := fmul_le t0 (expNegLb32Nat e_t0)
      have h2 := expNegLb32Nat_le_exp e_t0
      have h3 : Real.exp (-((e_t0 : ℝ) / S_nat)) ≤ Real.exp (-((e_ub : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) := by
        rw [neg_mul]; exact Real.exp_le_exp.mpr (by linarith only [het0_le])
      have h4 := mul_le_mul_of_nonneg_left (le_trans h2 h3) ht0_nn
      linarith only [h1, h4]
    have hu1 : ((fmul t1 (expNegLb32Nat e_t1) : ℕ) : ℝ) / S_nat ≤
        ((t1 : ℝ) / S_nat) * Real.exp (-((e_ub : ℝ) / S_nat) * ((t1 : ℝ) / S_nat)) := by
      have h1 := fmul_le t1 (expNegLb32Nat e_t1)
      have h2 := expNegLb32Nat_le_exp e_t1
      have h3 : Real.exp (-((e_t1 : ℝ) / S_nat)) ≤ Real.exp (-((e_ub : ℝ) / S_nat) * ((t1 : ℝ) / S_nat)) := by
        rw [neg_mul]; exact Real.exp_le_exp.mpr (by linarith only [het1_le])
      have h4 := mul_le_mul_of_nonneg_left (le_trans h2 h3) (by positivity : 0 ≤ (t1 : ℝ) / S_nat)
      linarith only [h1, h4]
    have humin_cast : (u_min : ℝ) / S_nat =
        min (((fmul t0 (expNegLb32Nat e_t0) : ℕ) : ℝ) / S_nat)
            (((fmul t1 (expNegLb32Nat e_t1) : ℕ) : ℝ) / S_nat) := by
      dsimp [u_min]; push_cast
      rw [min_div_div_right hS.le]
    have hmin_le : (u_min : ℝ) / S_nat ≤
        min (((t0 : ℝ) / S_nat) * Real.exp (-((e_ub : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)))
            (((t1 : ℝ) / S_nat) * Real.exp (-((e_ub : ℝ) / S_nat) * ((t1 : ℝ) / S_nat))) := by
      rw [humin_cast]
      exact min_le_min hu0 hu1
    exact le_trans hmin_le (t_mul_exp_neg_ge_min he_ub_nn ht0_nn ht0 ht1)
  have hexp_diff : Real.exp (-((e_ub : ℝ) / S_nat) * t) * Real.exp (-y ^ 2 * t) ≤
      Real.exp (-((y + k) ^ 2 + δ ^ 2) * t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : (y + k) ^ 2 + δ ^ 2 = y ^ 2 + (2 * k * y + k ^ 2 + δ ^ 2) := by ring
    rw [hsq]
    nlinarith only [he_ub_le, ht0, ht0_nn]
  have hstep_le : ((okC1Step k y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat ≤
      2 * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) * ((u_min : ℝ) / S_nat) := by
    have h1 := fmul_le (2 * fmul yk_lo sinh_lb) u_min
    have h2 := fmul_le yk_lo sinh_lb
    have h3 : ((2 * fmul yk_lo sinh_lb : ℕ) : ℝ) / S_nat ≤ 2 * (((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat)) := by
      have hcast : ((2 * fmul yk_lo sinh_lb : ℕ) : ℝ) / S_nat = 2 * (((fmul yk_lo sinh_lb : ℕ) : ℝ) / S_nat) := by
        push_cast; ring
      rw [hcast]; linarith only [h2]
    have h4 := mul_le_mul_of_nonneg_right h3 (div_nonneg (Nat.cast_nonneg u_min) hS.le)
    have h4' : 2 * ((yk_lo : ℝ) / S_nat * ((sinh_lb : ℝ) / S_nat)) * ((u_min : ℝ) / S_nat) =
        2 * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) * ((u_min : ℝ) / S_nat) := by ring
    have hok_def : okC1Step k y0 y1 t0 t1 d0 d1 = fmul (2 * fmul yk_lo sinh_lb) u_min := rfl
    rw [hok_def]
    linarith only [h1, h4, h4']
  have hcomb : ((okC1Step k y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) ≤
      2 * (Real.exp (-((e_ub : ℝ) / S_nat) * t) * Real.exp (-y ^ 2 * t)) *
        (2 * δ * t * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat)) := by
    have hA : ((okC1Step k y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) ≤
        (2 * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) * ((u_min : ℝ) / S_nat)) *
          (2 * δ * Real.exp (-y ^ 2 * t)) :=
      mul_le_mul_of_nonneg_right hstep_le (by positivity)
    have hB : (2 * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) * ((u_min : ℝ) / S_nat)) *
          (2 * δ * Real.exp (-y ^ 2 * t)) ≤
        (2 * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) * (t * Real.exp (-((e_ub : ℝ) / S_nat) * t))) *
          (2 * δ * Real.exp (-y ^ 2 * t)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht_exp (by positivity)) (by positivity)
    have hEq : (2 * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat) * (t * Real.exp (-((e_ub : ℝ) / S_nat) * t))) *
          (2 * δ * Real.exp (-y ^ 2 * t)) =
        2 * (Real.exp (-((e_ub : ℝ) / S_nat) * t) * Real.exp (-y ^ 2 * t)) *
          (2 * δ * t * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat)) := by ring
    exact le_trans hA (le_trans hB (le_of_eq hEq))
  have hcomb2 : 2 * (Real.exp (-((e_ub : ℝ) / S_nat) * t) * Real.exp (-y ^ 2 * t)) *
        (2 * δ * t * ((yk_lo : ℝ) / S_nat) * ((sinh_lb : ℝ) / S_nat)) ≤
      2 * Real.exp (-((y + k) ^ 2 + δ ^ 2) * t) *
        ((Real.exp (2 * (y + k) * δ * t) - Real.exp (-(2 * (y + k) * δ * t))) / 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hexp_diff (by norm_num)) hsinh_bound (by positivity) (by positivity)
  rw [hsinh_exp]; exact le_trans hcomb hcomb2

private lemma okC1Nat_sound {y0 y1 t0 t1 d0 d1 : ℕ}
    (hy01 : y0 ≤ y1) (ht01 : t0 ≤ t1) (hd01 : d0 < d1)
    (hy_lo : S_nat / 4 ≤ y0) (ht_lo : 7 * S_nat / 10 ≤ t0) (_hd_hi : d1 ≤ S_nat / 4)
    (hok : okC1Nat y0 y1 t0 t1 d0 d1 = true)
    {y t δ : ℝ} (hy0 : (y0 : ℝ) / S_nat ≤ y) (hy1 : y ≤ (y1 : ℝ) / S_nat)
    (ht0 : (t0 : ℝ) / S_nat ≤ t) (ht1 : t ≤ (t1 : ℝ) / S_nat)
    (hd0 : (d0 : ℝ) / S_nat < δ) (hd1 : δ ≤ (d1 : ℝ) / S_nat)
    (h1a_neg : y * t < 3 / 4) (h1b_neg : 2 * (y - δ) ^ 2 * t < 1) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hδ : 0 < δ := lt_of_le_of_lt (by positivity) hd0
  have ht : 0 < t := lt_of_lt_of_le (by
    have : (7 * S_nat / 10 : ℕ) ≤ t0 := ht_lo
    have : 0 < t0 := by dsimp [S_nat] at this; omega
    positivity) ht0
  dsimp [okC1Nat] at hok
  split_ifs at hok with h1a h1b
  · exfalso
    have hr : 3 * ((S_nat : ℝ) * S_nat) ≤ 4 * ((y0 : ℝ) * t0) := by
      have hnat : 3 * (S_nat * S_nat) ≤ 4 * (y0 * t0) := by simpa [Nat.mul_assoc] using h1a
      exact_mod_cast hnat
    have hprod : 3 / 4 ≤ ((y0 : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by norm_num) (mul_pos hS hS)]
      linarith only [hr]
    have hyt : ((y0 : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) ≤ y * t :=
      mul_le_mul hy0 ht0 (div_nonneg (Nat.cast_nonneg _) hS.le) (le_trans (div_nonneg (Nat.cast_nonneg _) hS.le) hy0)
    linarith only [hprod, hyt, h1a_neg]
  · exfalso
    rcases h1b with ⟨hyd, h2⟩
    have hdiff : ((y0 - d1 : ℕ) : ℝ) / S_nat ≤ y - δ := by
      rw [Nat.cast_sub hyd, sub_div]; linarith only [hy0, hd1]
    have hnn : 0 ≤ ((y0 - d1 : ℕ) : ℝ) / S_nat := div_nonneg (Nat.cast_nonneg _) hS.le
    have hsq : (((y0 - d1 : ℕ) : ℝ) / S_nat) ^ 2 ≤ (y - δ) ^ 2 := pow_le_pow_left₀ hnn hdiff 2
    have hr : (S_nat : ℝ) ^ 3 ≤ 2 * ((y0 - d1 : ℕ) : ℝ) ^ 2 * t0 := by
      have : S_nat * S_nat * S_nat ≤ 2 * (y0 - d1) * (y0 - d1) * t0 := h2
      have hcast : (S_nat : ℝ) * S_nat * S_nat ≤ 2 * ((y0 - d1 : ℕ) : ℝ) * ((y0 - d1 : ℕ) : ℝ) * t0 := by
        exact_mod_cast this
      linarith only [hcast, show (S_nat : ℝ) ^ 3 = S_nat * S_nat * S_nat by ring,
        show 2 * ((y0 - d1 : ℕ) : ℝ) ^ 2 * t0 = 2 * ((y0 - d1 : ℕ) : ℝ) * ((y0 - d1 : ℕ) : ℝ) * t0 by ring]
    have hprod : 1 ≤ 2 * (((y0 - d1 : ℕ) : ℝ) / S_nat) ^ 2 * ((t0 : ℝ) / S_nat) := by
      have heq : 2 * (((y0 - d1 : ℕ) : ℝ) / S_nat) ^ 2 * ((t0 : ℝ) / S_nat) =
          (2 * ((y0 - d1 : ℕ) : ℝ) ^ 2 * t0) / (S_nat : ℝ) ^ 3 := by ring
      rw [heq, one_le_div (pow_pos hS 3)]
      exact hr
    have hyt : 2 * (((y0 - d1 : ℕ) : ℝ) / S_nat) ^ 2 * ((t0 : ℝ) / S_nat) ≤ 2 * (y - δ) ^ 2 * t := by
      have hm := mul_le_mul hsq ht0 (div_nonneg (Nat.cast_nonneg _) hS.le) (sq_nonneg _)
      linarith only [hm]
    linarith only [hprod, hyt, h1b_neg]
  · rw [decide_eq_true_eq] at hok
    set v_a := d0 * (2 * y0 - d0)
    set v_b := d1 * (2 * y0 - d1)
    set a0_lb := fmul (min v_a v_b / S_nat) t0
    set u0 := fmul y0 t0
    set du0_lb := fmul d1 u0
    set du0_ub := cmul d1 u0
    set du0_sq_ub := cmul du0_ub du0_ub
    set den0 := S_nat + 4 * du0_ub + 8 * du0_sq_ub
    set frac0 := fdiv (2 * fmul u0 (S_nat + 2 * du0_lb)) den0
    have hy0_r_ge : (1 / 4 : ℝ) ≤ (y0 : ℝ) / S_nat := by
      have h1 : ((S_nat / 4 : ℕ) : ℝ) ≤ y0 := by exact_mod_cast hy_lo
      have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
      have h3 := div_le_div_of_nonneg_right h1 hS.le
      linarith only [h2, h3]
    have hd1_r_le : (d1 : ℝ) / S_nat ≤ 1 / 4 := by
      have h1 : (d1 : ℝ) ≤ ((S_nat / 4 : ℕ) : ℝ) := by exact_mod_cast _hd_hi
      have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
      have h3 := div_le_div_of_nonneg_right h1 hS.le
      linarith only [h2, h3]
    have hy_ge : 1 / 4 ≤ y := le_trans hy0_r_ge hy0
    have ha0_le : (a0_lb : ℝ) / S_nat ≤ δ * (2 * y - δ) * t := by
      have hd0_r : (d0 : ℝ) / S_nat ≤ δ := hd0.le
      have hd1_r : δ ≤ (d1 : ℝ) / S_nat := hd1
      have h2y_d0 : d0 ≤ 2 * y0 := by dsimp [S_nat] at *; omega
      have h2y_d1 : d1 ≤ 2 * y0 := by dsimp [S_nat] at *; omega
      have hid : ((d1 : ℝ) / S_nat - (d0 : ℝ) / S_nat) * (δ * (2 * ((y0 : ℝ) / S_nat) - δ)) =
          ((d1 : ℝ) / S_nat - δ) * (((d0 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d0 : ℝ) / S_nat)) +
          (δ - (d0 : ℝ) / S_nat) * (((d1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d1 : ℝ) / S_nat)) +
          ((d1 : ℝ) / S_nat - (d0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat - δ) * (δ - (d0 : ℝ) / S_nat) := by ring
      have hd_pos : 0 < (d1 : ℝ) / S_nat - (d0 : ℝ) / S_nat := by
        have : (d0 : ℝ) < d1 := by exact_mod_cast hd01
        exact sub_pos.mpr (div_lt_div_of_pos_right this hS)
      have hmin_quad : min (((d0 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d0 : ℝ) / S_nat))
          (((d1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d1 : ℝ) / S_nat)) ≤ δ * (2 * y - δ) := by
        set m := min (((d0 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d0 : ℝ) / S_nat))
          (((d1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d1 : ℝ) / S_nat))
        have h1 : m ≤ ((d0 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d0 : ℝ) / S_nat) := min_le_left _ _
        have h2 : m ≤ ((d1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d1 : ℝ) / S_nat) := min_le_right _ _
        have hpos_rem : 0 ≤ ((d1 : ℝ) / S_nat - (d0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat - δ) * (δ - (d0 : ℝ) / S_nat) :=
          mul_nonneg (mul_nonneg hd_pos.le (by linarith only [hd1_r])) (by linarith only [hd0_r])
        have hm_mul : ((d1 : ℝ) / S_nat - (d0 : ℝ) / S_nat) * m ≤
            ((d1 : ℝ) / S_nat - (d0 : ℝ) / S_nat) * (δ * (2 * ((y0 : ℝ) / S_nat) - δ)) := by
          have ha := mul_le_mul_of_nonneg_left h1 (by linarith only [hd1_r] : 0 ≤ (d1 : ℝ) / S_nat - δ)
          have hb := mul_le_mul_of_nonneg_left h2 (by linarith only [hd0_r] : 0 ≤ δ - (d0 : ℝ) / S_nat)
          linarith only [hid, hpos_rem, ha, hb]
        have hm0 : m ≤ δ * (2 * ((y0 : ℝ) / S_nat) - δ) :=
          le_of_mul_le_mul_left hm_mul hd_pos
        have hm1 : 2 * ((y0 : ℝ) / S_nat) - δ ≤ 2 * y - δ := by linarith only [hy0]
        linarith only [hm0, mul_le_mul_of_nonneg_left hm1 hδ.le]
      have hcast_min : ((min v_a v_b / S_nat : ℕ) : ℝ) / S_nat ≤
          min (((d0 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d0 : ℝ) / S_nat))
              (((d1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d1 : ℝ) / S_nat)) := by
        have hnat_div : (min v_a v_b / S_nat : ℕ) * S_nat ≤ min v_a v_b := Nat.div_mul_le_self _ _
        have hr_div : ((min v_a v_b / S_nat : ℕ) : ℝ) * S_nat ≤ (min v_a v_b : ℝ) := by exact_mod_cast hnat_div
        have hva : (v_a : ℝ) / (S_nat : ℝ) ^ 2 = ((d0 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d0 : ℝ) / S_nat) := by
          dsimp [v_a]; rw [Nat.cast_mul, Nat.cast_sub h2y_d0]; push_cast; field_simp
        have hvb : (v_b : ℝ) / (S_nat : ℝ) ^ 2 = ((d1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - (d1 : ℝ) / S_nat) := by
          dsimp [v_b]; rw [Nat.cast_mul, Nat.cast_sub h2y_d1]; push_cast; field_simp
        have hmin_r : (min v_a v_b : ℝ) / (S_nat : ℝ) ^ 2 =
            min ((v_a : ℝ) / (S_nat : ℝ) ^ 2) ((v_b : ℝ) / (S_nat : ℝ) ^ 2) := by
          rw [min_div_div_right (by positivity)]
        rw [← hva, ← hvb, ← hmin_r, div_le_div_iff₀ hS (by positivity)]
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hr_div hS.le
      have hmin_nn : 0 ≤ ((min v_a v_b / S_nat : ℕ) : ℝ) / S_nat := by positivity
      have hfmul := fmul_le (min v_a v_b / S_nat) t0
      have hy2δ_nn : 0 ≤ 2 * y - δ := by linarith only [hy_ge, hd1, hd1_r_le]
      have hm := mul_le_mul (le_trans hcast_min hmin_quad) ht0 (by positivity) (mul_nonneg hδ.le hy2δ_nn)
      linarith only [hfmul, hm]
    clear_value v_a v_b
    have hu0_nat : 0 < u0 := by
      dsimp [u0, fmul]
      exact Nat.div_pos (le_trans (by norm_num [S_nat]) (Nat.mul_le_mul hy_lo ht_lo)) (by norm_num [S_nat])
    have hu0_r_pos : (0 : ℝ) < u0 := by exact_mod_cast hu0_nat
    have hu0_pos : 0 < (u0 : ℝ) / S_nat := div_pos hu0_r_pos hS
    have hu0_le : (u0 : ℝ) / S_nat ≤ y * t := by
      have hfm := fmul_le y0 t0
      have hm := mul_le_mul hy0 ht0 (by positivity) (by linarith only [hy_ge])
      linarith only [hfm, hm]
    have hd1_pos : 0 < (d1 : ℝ) / S_nat := lt_of_lt_of_le hδ hd1
    have hd1_r_pos : (0 : ℝ) < d1 := by
      by_contra hle; push Not at hle
      have : (d1 : ℝ) / S_nat ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle hS.le
      linarith only [hd1_pos, this]
    have hfrac_le : (frac0 : ℝ) / S_nat ≤ (1 - Real.exp (-4 * y * t * δ)) / (2 * δ) := by
      have hexp1 : 1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * δ) ≤ 1 - Real.exp (-4 * y * t * δ) := by
        have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu0_le (by norm_num : (0 : ℝ) ≤ 4)) hδ.le
        have hex := Real.exp_le_exp.mpr (neg_le_neg hmul)
        rw [show -((4 : ℝ) * (y * t) * δ) = -4 * y * t * δ by ring,
            show -((4 : ℝ) * ((u0 : ℝ) / S_nat) * δ) = -4 * ((u0 : ℝ) / S_nat) * δ by ring] at hex
        linarith only [hex]
      have hdiv1 : (1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * δ)) / (2 * δ) ≤ (1 - Real.exp (-4 * y * t * δ)) / (2 * δ) :=
        div_le_div_of_nonneg_right hexp1 (by positivity)
      have hant := one_sub_exp_neg_div_antitone
        (by simp only [Set.mem_Ioi]; positivity : 4 * ((u0 : ℝ) / S_nat) * δ ∈ Set.Ioi 0)
        (by simp only [Set.mem_Ioi]; positivity : 4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat) ∈ Set.Ioi 0)
        (mul_le_mul_of_nonneg_left hd1 (by positivity : 0 ≤ 4 * ((u0 : ℝ) / S_nat)) :
          4 * ((u0 : ℝ) / S_nat) * δ ≤ 4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat))
      have hdiv2 : (1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat))) / (2 * ((d1 : ℝ) / S_nat)) ≤
          (1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * δ)) / (2 * δ) := by
        have hmul := mul_le_mul_of_nonneg_left hant (by positivity : 0 ≤ 2 * ((u0 : ℝ) / S_nat))
        have heqL : 2 * ((u0 : ℝ) / S_nat) * ((1 - Real.exp (-(4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat)))) /
            (4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat))) =
            (1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat))) / (2 * ((d1 : ℝ) / S_nat)) := by
          have ha : -(4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat)) = -4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat) := by ring
          rw [ha]; field_simp [hu0_r_pos.ne', hd1_r_pos.ne', hS.ne']; ring
        have heqR : 2 * ((u0 : ℝ) / S_nat) * ((1 - Real.exp (-(4 * ((u0 : ℝ) / S_nat) * δ))) /
            (4 * ((u0 : ℝ) / S_nat) * δ)) =
            (1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * δ)) / (2 * δ) := by
          have ha : -(4 * ((u0 : ℝ) / S_nat) * δ) = -4 * ((u0 : ℝ) / S_nat) * δ := by ring
          rw [ha]; field_simp [hu0_r_pos.ne', hδ.ne', hS.ne']; ring
        linarith only [hmul, heqL, heqR]
      set z := ((d1 : ℝ) / S_nat) * ((u0 : ℝ) / S_nat)
      have hz_nn : 0 ≤ z := by positivity
      have hpoly := one_sub_exp_neg_ge (by positivity : 0 ≤ 4 * z)
      have hpoly_div : 2 * ((u0 : ℝ) / S_nat) * (1 + 2 * z) / (1 + 4 * z + 8 * z ^ 2) ≤
          (1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat))) / (2 * ((d1 : ℝ) / S_nat)) := by
        have hpos_den : 0 < 1 + 4 * z + 8 * z ^ 2 := by positivity
        have h1 := div_le_div_of_nonneg_right hpoly (by positivity : 0 ≤ 2 * ((d1 : ℝ) / S_nat))
        have hden_eq : 1 + 4 * z + (4 * z) ^ 2 / 2 = 1 + 4 * z + 8 * z ^ 2 := by ring
        have hnum_eq : 4 * z + (4 * z) ^ 2 / 2 = 4 * z * (1 + 2 * z) := by ring
        have heqL : (4 * z + (4 * z) ^ 2 / 2) / (1 + 4 * z + (4 * z) ^ 2 / 2) / (2 * ((d1 : ℝ) / S_nat)) =
            2 * ((u0 : ℝ) / S_nat) * (1 + 2 * z) / (1 + 4 * z + 8 * z ^ 2) := by
          rw [hden_eq, hnum_eq]; dsimp [z]; field_simp [hd1_r_pos.ne', hS.ne']; ring
        have heqR : (1 - Real.exp (-(4 * z))) / (2 * ((d1 : ℝ) / S_nat)) =
            (1 - Real.exp (-4 * ((u0 : ℝ) / S_nat) * ((d1 : ℝ) / S_nat))) / (2 * ((d1 : ℝ) / S_nat)) := by
          dsimp [z]; ring_nf
        linarith only [h1, heqL, heqR]
      have hnum_le : ((2 * fmul u0 (S_nat + 2 * du0_lb) : ℕ) : ℝ) / S_nat ≤ 2 * ((u0 : ℝ) / S_nat) * (1 + 2 * z) := by
        have h1 := fmul_le u0 (S_nat + 2 * du0_lb)
        have h2 : (du0_lb : ℝ) / S_nat ≤ z := fmul_le d1 u0
        have hcast : ((S_nat + 2 * du0_lb : ℕ) : ℝ) / S_nat = 1 + 2 * ((du0_lb : ℝ) / S_nat) := by
          push_cast; field_simp
        have hcast2 : ((2 * fmul u0 (S_nat + 2 * du0_lb) : ℕ) : ℝ) / S_nat =
            2 * (((fmul u0 (S_nat + 2 * du0_lb) : ℕ) : ℝ) / S_nat) := by push_cast; ring
        rw [hcast2]
        have hm := mul_le_mul_of_nonneg_left
          (by linarith only [h2, hcast] : ((S_nat + 2 * du0_lb : ℕ) : ℝ) / S_nat ≤ 1 + 2 * z)
          hu0_pos.le
        linarith only [h1, hm]
      have hden_le : 1 + 4 * z + 8 * z ^ 2 ≤ (den0 : ℝ) / S_nat := by
        have h1 : z ≤ (du0_ub : ℝ) / S_nat := le_cmul d1 u0
        have h2 : z ^ 2 ≤ (du0_sq_ub : ℝ) / S_nat := by
          have hcm := le_cmul du0_ub du0_ub
          have hsq : z ^ 2 ≤ ((du0_ub : ℝ) / S_nat) ^ 2 := pow_le_pow_left₀ hz_nn h1 2
          rw [sq ((du0_ub : ℝ) / S_nat)] at hsq
          exact le_trans hsq hcm
        have hcast : (den0 : ℝ) / S_nat = 1 + 4 * ((du0_ub : ℝ) / S_nat) + 8 * ((du0_sq_ub : ℝ) / S_nat) := by
          dsimp [den0]; push_cast; field_simp
        linarith only [h1, h2, hcast]
      have hden0_pos : 0 < den0 := by dsimp [den0, S_nat]; omega
      have hfrac_cmp : (frac0 : ℝ) / S_nat ≤
          2 * ((u0 : ℝ) / S_nat) * (1 + 2 * z) / (1 + 4 * z + 8 * z ^ 2) := by
        have h1 := fdiv_le (2 * fmul u0 (S_nat + 2 * du0_lb)) den0 hden0_pos
        have h2 : ((2 * fmul u0 (S_nat + 2 * du0_lb) : ℕ) : ℝ) / den0 =
            (((2 * fmul u0 (S_nat + 2 * du0_lb) : ℕ) : ℝ) / S_nat) / ((den0 : ℝ) / S_nat) := by
          field_simp
        have h4 : (2 * ((u0 : ℝ) / S_nat) * (1 + 2 * z)) / ((den0 : ℝ) / S_nat) ≤
            (2 * ((u0 : ℝ) / S_nat) * (1 + 2 * z)) / (1 + 4 * z + 8 * z ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden_le
        linarith only [div_le_div_of_nonneg_right hnum_le (by positivity : 0 ≤ (den0 : ℝ) / S_nat), h1, h2, h4]
      exact le_trans hfrac_cmp (le_trans hpoly_div (le_trans hdiv2 hdiv1))
    clear_value u0 du0_lb du0_ub du0_sq_ub den0
    have hk0 : ((fmul (S_nat + a0_lb) frac0 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) ≤
        Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y + δ) ^ 2 * t) := by
      have hexp_ge : ((S_nat + a0_lb : ℕ) : ℝ) / S_nat ≤ Real.exp (δ * (2 * y - δ) * t) := by
        have hcast : ((S_nat + a0_lb : ℕ) : ℝ) / S_nat = 1 + (a0_lb : ℝ) / S_nat := by push_cast; field_simp
        rw [hcast]
        exact le_trans (by linarith only [ha0_le]) (Real.add_one_le_exp (δ * (2 * y - δ) * t))
      have hfm := fmul_le (S_nat + a0_lb) frac0
      have hmul1 : ((fmul (S_nat + a0_lb) frac0 : ℕ) : ℝ) / S_nat ≤
          Real.exp (δ * (2 * y - δ) * t) * ((1 - Real.exp (-4 * y * t * δ)) / (2 * δ)) := by
        have hmul := mul_le_mul hexp_ge hfrac_le (by positivity) (Real.exp_pos _).le
        linarith only [hfm, hmul]
      have hmul2 := mul_le_mul_of_nonneg_right hmul1 (by positivity : 0 ≤ 2 * δ * Real.exp (-y ^ 2 * t))
      have heqR : Real.exp (δ * (2 * y - δ) * t) * ((1 - Real.exp (-4 * y * t * δ)) / (2 * δ)) *
            (2 * δ * Real.exp (-y ^ 2 * t)) =
          Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y + δ) ^ 2 * t) := by
        have h1 : Real.exp (δ * (2 * y - δ) * t) * Real.exp (-y ^ 2 * t) = Real.exp (-(y - δ) ^ 2 * t) := by
          rw [← Real.exp_add]; congr 1; ring
        have h2 : Real.exp (-(y - δ) ^ 2 * t) * Real.exp (-4 * y * t * δ) = Real.exp (-(y + δ) ^ 2 * t) := by
          rw [← Real.exp_add]; congr 1; ring
        calc Real.exp (δ * (2 * y - δ) * t) * ((1 - Real.exp (-4 * y * t * δ)) / (2 * δ)) *
              (2 * δ * Real.exp (-y ^ 2 * t))
            = (Real.exp (δ * (2 * y - δ) * t) * Real.exp (-y ^ 2 * t)) * (1 - Real.exp (-4 * y * t * δ)) := by
              field_simp
          _ = Real.exp (-(y - δ) ^ 2 * t) * (1 - Real.exp (-4 * y * t * δ)) := by rw [h1]
          _ = Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y - δ) ^ 2 * t) * Real.exp (-4 * y * t * δ) := by ring
          _ = Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y + δ) ^ 2 * t) := by rw [h2]
      linarith only [hmul2, heqR]
    have hk1 := okC1Step_sound (k := 1) hy01 ht01 hd01.le hy0 hy1 ht0 ht1 hd0.le hd1 hδ
    have hk2 := okC1Step_sound (k := 2) hy01 ht01 hd01.le hy0 hy1 ht0 ht1 hd0.le hd1 hδ
    have hk3 := okC1Step_sound (k := 3) hy01 ht01 hd01.le hy0 hy1 ht0 ht1 hd0.le hd1 hδ
    have hs_all : Summable (fun k : ℕ => Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
      have hpb := (P5_gauss_bounds (y - 1 / 2) δ t hδ ht).1
      exact hpb.congr fun k => by ring_nf
    have hsum4 : ∑ k ∈ Finset.range 4, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) ≤
        ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) :=
      Summable.sum_le_tsum (Finset.range 4) (fun k _ => h_gauss_nonneg (by linarith only [hy_ge, hd1, hd1_r_le]) hδ.le ht.le) hs_all
    have h4exp : ∑ k ∈ Finset.range 4, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) =
        (Real.exp (-(y - δ) ^ 2 * t) - Real.exp (-(y + δ) ^ 2 * t)) +
        (Real.exp (-(y + (1 : ℕ) - δ) ^ 2 * t) - Real.exp (-(y + (1 : ℕ) + δ) ^ 2 * t)) +
        (Real.exp (-(y + (2 : ℕ) - δ) ^ 2 * t) - Real.exp (-(y + (2 : ℕ) + δ) ^ 2 * t)) +
        (Real.exp (-(y + (3 : ℕ) - δ) ^ 2 * t) - Real.exp (-(y + (3 : ℕ) + δ) ^ 2 * t)) := by
      simp [Finset.sum_range_succ]; ring
    have hs_real : 1 ≤ ((fmul (S_nat + a0_lb) frac0 + okC1Step 1 y0 y1 t0 t1 d0 d1 +
        okC1Step 2 y0 y1 t0 t1 d0 d1 + okC1Step 3 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat := by
      have hcast : (S_nat : ℝ) ≤ ((fmul (S_nat + a0_lb) frac0 + okC1Step 1 y0 y1 t0 t1 d0 d1 +
          okC1Step 2 y0 y1 t0 t1 d0 d1 + okC1Step 3 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) := by
        exact_mod_cast hok
      rwa [one_le_div hS]
    have hmul_s : 2 * δ * Real.exp (-y ^ 2 * t) ≤
        (((fmul (S_nat + a0_lb) frac0 + okC1Step 1 y0 y1 t0 t1 d0 d1 +
          okC1Step 2 y0 y1 t0 t1 d0 d1 + okC1Step 3 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat) *
          (2 * δ * Real.exp (-y ^ 2 * t)) := by
      calc 2 * δ * Real.exp (-y ^ 2 * t)
          = 1 * (2 * δ * Real.exp (-y ^ 2 * t)) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hs_real (by positivity)
    have hsplit : (((fmul (S_nat + a0_lb) frac0 + okC1Step 1 y0 y1 t0 t1 d0 d1 +
          okC1Step 2 y0 y1 t0 t1 d0 d1 + okC1Step 3 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat) *
          (2 * δ * Real.exp (-y ^ 2 * t)) =
        ((fmul (S_nat + a0_lb) frac0 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) +
        ((okC1Step 1 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) +
        ((okC1Step 2 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) +
        ((okC1Step 3 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) := by
      push_cast; ring
    have hk0123 : ((fmul (S_nat + a0_lb) frac0 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) +
        ((okC1Step 1 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) +
        ((okC1Step 2 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) +
        ((okC1Step 3 y0 y1 t0 t1 d0 d1 : ℕ) : ℝ) / S_nat * (2 * δ * Real.exp (-y ^ 2 * t)) ≤
        ∑ k ∈ Finset.range 4, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
      rw [h4exp]
      exact add_le_add (add_le_add (add_le_add hk0 hk1) hk2) hk3
    exact le_trans hmul_s (le_trans (le_of_eq hsplit) (le_trans hk0123 hsum4))

private lemma verifyTree_c1_sound :
    ∀ (tr : BoxTree) (y0 y1 t0 t1 d0 d1 : ℕ),
      S_nat / 4 ≤ y0 → 7 * S_nat / 10 ≤ t0 → d1 ≤ S_nat / 4 →
      verifyTree okC1Nat tr y0 y1 t0 t1 d0 d1 = true →
      ∀ {y t δ : ℝ}, (y0 : ℝ) / S_nat ≤ y → y ≤ (y1 : ℝ) / S_nat →
        (t0 : ℝ) / S_nat ≤ t → t ≤ (t1 : ℝ) / S_nat →
        (d0 : ℝ) / S_nat < δ → δ ≤ (d1 : ℝ) / S_nat →
        y * t < 3 / 4 → 2 * (y - δ) ^ 2 * t < 1 →
        2 * δ * Real.exp (-y ^ 2 * t) ≤
          ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t))
  | .leaf, y0, y1, t0, t1, d0, d1, hy_lo, ht_lo, hd_hi, hok, y, t, δ, hy0, hy1, ht0, ht1, hd0, hd1, h1a, h1b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact okC1Nat_sound hok.1.1 hok.1.2.1 hok.1.2.2 hy_lo ht_lo hd_hi hok.2 hy0 hy1 ht0 ht1 hd0 hd1 h1a h1b
  | .splitY ym l r, y0, y1, t0, t1, d0, d1, hy_lo, ht_lo, hd_hi, hok, y, t, δ, hy0, hy1, ht0, ht1, hd0, hd1, h1a, h1b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases hym : y ≤ (ym : ℝ) / S_nat
    · exact verifyTree_c1_sound l y0 ym t0 t1 d0 d1 hy_lo ht_lo hd_hi hok.1.2 hy0 hym ht0 ht1 hd0 hd1 h1a h1b
    · exact verifyTree_c1_sound r ym y1 t0 t1 d0 d1 (le_trans hy_lo hok.1.1.1) ht_lo hd_hi hok.2
        (le_of_not_ge hym) hy1 ht0 ht1 hd0 hd1 h1a h1b
  | .splitT tm l r, y0, y1, t0, t1, d0, d1, hy_lo, ht_lo, hd_hi, hok, y, t, δ, hy0, hy1, ht0, ht1, hd0, hd1, h1a, h1b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases htm : t ≤ (tm : ℝ) / S_nat
    · exact verifyTree_c1_sound l y0 y1 t0 tm d0 d1 hy_lo ht_lo hd_hi hok.1.2 hy0 hy1 ht0 htm hd0 hd1 h1a h1b
    · exact verifyTree_c1_sound r y0 y1 tm t1 d0 d1 hy_lo (le_trans ht_lo hok.1.1.1) hd_hi hok.2
        hy0 hy1 (le_of_not_ge htm) ht1 hd0 hd1 h1a h1b
  | .splitX xm l r, y0, y1, t0, t1, d0, d1, hy_lo, ht_lo, hd_hi, hok, y, t, δ, hy0, hy1, ht0, ht1, hd0, hd1, h1a, h1b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases hxm : δ ≤ (xm : ℝ) / S_nat
    · exact verifyTree_c1_sound l y0 y1 t0 t1 d0 xm hy_lo ht_lo (le_trans hok.1.1.2 hd_hi) hok.1.2
        hy0 hy1 ht0 ht1 hd0 hxm h1a h1b
    · exact verifyTree_c1_sound r y0 y1 t0 t1 xm d1 hy_lo ht_lo hd_hi hok.2
        hy0 hy1 ht0 ht1 (lt_of_not_ge hxm) hd1 h1a h1b


lemma gaussian_sum_ge_c1_box_aux {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hy_hi : y ≤ 11 / 10)
    (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (ht_lo : 7 / 10 < t) (ht_hi : t ≤ 3)
    (h1a_neg : y * t < 3 / 4) (h1b_neg : 2 * (y - δ) ^ 2 * t < 1) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  have hy_lo : ((S_nat / 4 : ℕ) : ℝ) / S_nat ≤ y := by
    have : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [this, hy]
  have hy_hi' : y ≤ ((11 * S_nat / 10 : ℕ) : ℝ) / S_nat := by
    have : ((11 * S_nat / 10 : ℕ) : ℝ) / S_nat = 11 / 10 := by norm_num [S_nat]
    linarith only [this, hy_hi]
  have ht_lo' : ((7 * S_nat / 10 : ℕ) : ℝ) / S_nat ≤ t := by
    have : ((7 * S_nat / 10 : ℕ) : ℝ) / S_nat = 7 / 10 := by norm_num [S_nat]
    linarith only [this, ht_lo]
  have ht_hi' : t ≤ ((3 * S_nat : ℕ) : ℝ) / S_nat := by
    have : ((3 * S_nat : ℕ) : ℝ) / S_nat = 3 := by norm_num [S_nat]
    linarith only [this, ht_hi]
  by_cases hδ18 : δ ≤ 1 / 8
  · refine verifyTree_c1_sound c1aTree (S_nat / 4) (11 * S_nat / 10) (7 * S_nat / 10) (3 * S_nat)
      0 (S_nat / 8) le_rfl le_rfl (by norm_num [S_nat]) c1a_verified hy_lo hy_hi' ht_lo' ht_hi'
      (by simp [hδ0]) ?_ h1a_neg h1b_neg
    have : ((S_nat / 8 : ℕ) : ℝ) / S_nat = 1 / 8 := by norm_num [S_nat]
    linarith only [this, hδ18]
  · have hδ_gt18 : 1 / 8 < δ := lt_of_not_ge hδ18
    refine verifyTree_c1_sound c1bTree (S_nat / 4) (11 * S_nat / 10) (7 * S_nat / 10) (3 * S_nat)
      (S_nat / 8) (S_nat / 4) le_rfl le_rfl le_rfl c1b_verified hy_lo hy_hi' ht_lo' ht_hi' ?_ ?_
      h1a_neg h1b_neg
    · have : ((S_nat / 8 : ℕ) : ℝ) / S_nat = 1 / 8 := by norm_num [S_nat]
      linarith only [this, hδ_gt18]
    · have : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
      linarith only [this, hδ_le]

end SolGammaHelpers

theorem solution {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hy_hi : y ≤ 11 / 10)
    (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (ht_lo : 7 / 10 < t) (ht_hi : t ≤ 3)
    (h1a_neg : y * t < 3 / 4) (h1b_neg : 2 * (y - δ) ^ 2 * t < 1) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) :=
  SolGammaHelpers.gaussian_sum_ge_c1_box_aux hy hy_hi hδ0 hδ_le ht_lo ht_hi h1a_neg h1b_neg
