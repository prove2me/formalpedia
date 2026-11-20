-- Prove2me | solution 1 for RademacherGamma_gaussian_sum_ge_2b_p3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:17:33.111713+00:00
-- url     : https://prove2.me/submissions/e3d97aab-c2d2-4bbb-807e-0bff9afe2b3a

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


private lemma gaussian_integral_ub_2b {y η t : ℝ} (hy : 1 / 4 ≤ y) (hη0 : 0 < η)
    (hη_le : η ≤ 1 / 4) (ht : 0 < t) (ht_ub : t ≤ 7 / 10) (hx_le : 2 * y * η * t ≤ 3 / 5) :
    ∫ v in (y - η)..(y + η), Real.exp (-v ^ 2 * t) ≤
      (1 + (2 * y * η) ^ 2 * t ^ 2 / 6 + (2 * y * η) ^ 4 * t ^ 4 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) * t) *
        (2 * η * Real.exp (-y ^ 2 * t)) := by
  have hsh : ∫ v in (y - η)..(y + η), Real.exp (-v ^ 2 * t) =
      ∫ r in (-η)..η, Real.exp (-(y + r) ^ 2 * t) := by
    symm
    have heq : (fun r => Real.exp (-(y + r) ^ 2 * t)) = (fun r => Real.exp (-(r + y) ^ 2 * t)) := by
      ext r; ring_nf
    rw [heq, intervalIntegral.integral_comp_add_right (fun v => Real.exp (-v ^ 2 * t)) y]
    rw [show -η + y = y - η by ring, show η + y = y + η by ring]
  have hpt : ∀ r ∈ Set.Icc (-η) η, Real.exp (-(y + r) ^ 2 * t) ≤
      Real.exp (-y ^ 2 * t) * Real.exp (-2 * y * r * t) -
        Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t)) := by
    intro r _
    have heq : -(y + r) ^ 2 * t = -y ^ 2 * t + (-2 * y * r * t) + (-r ^ 2 * t) := by ring
    rw [heq, Real.exp_add, Real.exp_add]
    have h1 : Real.exp (-r ^ 2 * t) ≤ 1 - (r ^ 2 * t - r ^ 4 * t ^ 2 / 2) := by
      have hex := exp_neg_le_one_sub (by positivity : 0 ≤ r ^ 2 * t)
      rw [show -(r ^ 2 * t) = -r ^ 2 * t by ring, show (r ^ 2 * t) ^ 2 / 2 = r ^ 4 * t ^ 2 / 2 by ring] at hex
      linarith only [hex]
    have hm := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Real.exp (-y ^ 2 * t) * Real.exp (-2 * y * r * t))
    have hexp : Real.exp (-y ^ 2 * t) * Real.exp (-2 * y * r * t) * (1 - (r ^ 2 * t - r ^ 4 * t ^ 2 / 2)) =
        Real.exp (-y ^ 2 * t) * Real.exp (-2 * y * r * t) -
          Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t)) := by ring
    linarith only [hm, hexp]
  have hi := intervalIntegral.integral_mono_on (by linarith only [hη0])
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (-η) η)
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (-η) η) hpt
  rw [intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (-η) η)
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (-η) η)] at hi
  have hyt_pos : 0 < 2 * y * t := by nlinarith only [hy, ht]
  have hint1 : ∫ r in (-η)..η, Real.exp (-y ^ 2 * t) * Real.exp (-2 * y * r * t) ≤
      (1 + (2 * y * η * t) ^ 2 / 6 + (2 * y * η * t) ^ 4 / 100) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have hd1 : ∀ r : ℝ,
        HasDerivAt (fun x : ℝ => Real.exp (-y ^ 2 * t) * (Real.exp (-2 * y * x * t) / (-2 * y * t)))
          (Real.exp (-y ^ 2 * t) * Real.exp (-2 * y * r * t)) r := by
      intro r
      have ha : HasDerivAt (fun x : ℝ => -2 * y * x * t) (-2 * y * t) r :=
        (((hasDerivAt_id' r).const_mul (-2 * y)).mul_const t).congr_deriv (by ring)
      refine ((ha.exp.div_const (-2 * y * t)).const_mul (Real.exp (-y ^ 2 * t))).congr_deriv ?_
      have hne : -2 * y * t ≠ 0 := by linarith only [hyt_pos]
      field_simp [hne]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd1 r)
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (-η) η)
    have heval : ∫ r in (-η)..η, Real.exp (-y ^ 2 * t) * Real.exp (-2 * y * r * t) =
        Real.exp (-y ^ 2 * t) * ((Real.exp (2 * y * η * t) - Real.exp (-2 * y * η * t)) / (2 * y * t)) := by
      rw [hftc]
      have h1 : Real.exp (-2 * y * (-η) * t) = Real.exp (2 * y * η * t) := by congr 1; ring
      have h2 : Real.exp (-2 * y * η * t) = Real.exp (-(2 * y * η * t)) := by congr 1; ring
      rw [h1, h2]; field_simp [hyt_pos.ne']; ring
    have hsinh_poly : (Real.exp (2 * y * η * t) - Real.exp (-2 * y * η * t)) / 2 ≤
        (2 * y * η * t) + (2 * y * η * t) ^ 3 / 6 + (2 * y * η * t) ^ 5 / 100 := by
      let gs : ℝ → ℝ := fun x => x + x ^ 3 / 6 + x ^ 5 / 100 - (Real.exp x - Real.exp (-x)) / 2
      have hgs_der : ∀ x, HasDerivAt gs (1 + x ^ 2 / 2 + x ^ 4 / 20 - (Real.exp x + Real.exp (-x)) / 2) x := by
        intro x
        have h1 := ((hasDerivAt_id' x).fun_add ((hasDerivAt_pow 3 x).div_const 6)).fun_add
          ((hasDerivAt_pow 5 x).div_const 100)
        have h2 : HasDerivAt (fun u : ℝ => (Real.exp u - Real.exp (-u)) / 2) ((Real.exp x + Real.exp (-x)) / 2) x :=
          (((Real.hasDerivAt_exp x).fun_sub (hasDerivAt_neg x).exp).div_const 2).congr_deriv (by ring)
        exact (h1.fun_sub h2).congr_deriv (by norm_num; ring)
      have hmono : gs 0 ≤ gs (2 * y * η * t) :=
        monotoneOn_of_deriv_nonneg (convex_Icc 0 (3 / 5))
          (fun x _ => (hgs_der x).continuousAt.continuousWithinAt)
          (fun x _ => (hgs_der x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [interior_Icc] at hx
            rw [(hgs_der x).deriv]
            have hc := cosh_le_poly4 hx.1.le hx.2.le
            linarith only [hc])
          ⟨le_rfl, by norm_num⟩ ⟨by positivity, hx_le⟩ (by positivity)
      have hgs0 : gs 0 = 0 := by dsimp [gs]; norm_num
      dsimp [gs] at hmono
      have hmono' : 0 ≤ 2 * y * η * t + (2 * y * η * t) ^ 3 / 6 + (2 * y * η * t) ^ 5 / 100 -
          (Real.exp (2 * y * η * t) - Real.exp (-(2 * y * η * t))) / 2 := by
        simpa [hgs0] using hmono
      rw [show -(2 * y * η * t) = -2 * y * η * t by ring] at hmono'
      linarith only [hmono']
    have hdiv_sh : (Real.exp (2 * y * η * t) - Real.exp (-2 * y * η * t)) / (2 * y * t) ≤
        2 * η * (1 + (2 * y * η) ^ 2 * t ^ 2 / 6 + (2 * y * η) ^ 4 * t ^ 4 / 100) := by
      rw [div_le_iff₀ hyt_pos]
      have h1 : Real.exp (2 * y * η * t) - Real.exp (-2 * y * η * t) ≤
          2 * (2 * y * η * t + (2 * y * η * t) ^ 3 / 6 + (2 * y * η * t) ^ 5 / 100) := by
        linarith only [hsinh_poly]
      have h2 : 2 * η * (1 + (2 * y * η) ^ 2 * t ^ 2 / 6 + (2 * y * η) ^ 4 * t ^ 4 / 100) * (2 * y * t) =
          2 * (2 * y * η * t + (2 * y * η * t) ^ 3 / 6 + (2 * y * η * t) ^ 5 / 100) := by ring
      linarith only [h1, h2]
    have hm := mul_le_mul_of_nonneg_left hdiv_sh (Real.exp_pos (-y ^ 2 * t)).le
    have h3 : Real.exp (-y ^ 2 * t) * (2 * η * (1 + (2 * y * η) ^ 2 * t ^ 2 / 6 + (2 * y * η) ^ 4 * t ^ 4 / 100)) =
        (1 + (2 * y * η * t) ^ 2 / 6 + (2 * y * η * t) ^ 4 / 100) * (2 * η * Real.exp (-y ^ 2 * t)) := by ring
    linarith only [heval, hm, h3]
  have hint2 : (η ^ 2 / 3 - η ^ 4 * t / 10) * t * (2 * η * Real.exp (-y ^ 2 * t)) ≤
      ∫ r in (-η)..η, Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t)) := by
    have hsplit : ∫ r in (-η)..η, Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t)) =
        (∫ r in (-η)..0, Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t))) +
        (∫ r in 0..η, Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t))) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (-η) 0)
        (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 η)).symm
    have hflip : ∫ r in (-η)..0, Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t)) =
        ∫ r in 0..η, Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (2 * y * r * t)) := by
      have hrew : (fun r => Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t))) =
          (fun r => (fun u => Real.exp (-y ^ 2 * t) * ((u ^ 2 * t - u ^ 4 * t ^ 2 / 2) * Real.exp (2 * y * u * t))) (-r)) := by
        ext r; ring_nf
      rw [hrew, intervalIntegral.integral_comp_neg
        (f := fun u : ℝ => Real.exp (-y ^ 2 * t) * ((u ^ 2 * t - u ^ 4 * t ^ 2 / 2) * Real.exp (2 * y * u * t)))]
      simp only [neg_zero, neg_neg]
    rw [hsplit, hflip, ← intervalIntegral.integral_add
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 η)
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 η)]
    have hpt2 : ∀ r ∈ Set.Icc 0 η, Real.exp (-y ^ 2 * t) * (2 * (r ^ 2 * t - r ^ 4 * t ^ 2 / 2)) ≤
        Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (2 * y * r * t)) +
        Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t)) := by
      intro r hr
      have hr2t : r ^ 2 * t ≤ 1 := by nlinarith only [hr.1, hr.2, hη_le, ht, ht_ub]
      have hnn : 0 ≤ r ^ 2 * t := by positivity
      have hpos_r : 0 ≤ r ^ 2 * t - r ^ 4 * t ^ 2 / 2 := by
        nlinarith only [hr2t, hnn, show (r ^ 2 * t) ^ 2 = r ^ 4 * t ^ 2 by ring]
      have hcosh2 : 2 ≤ Real.exp (2 * y * r * t) + Real.exp (-2 * y * r * t) := by
        have ha := Real.add_one_le_exp (2 * y * r * t)
        have hb := Real.add_one_le_exp (-2 * y * r * t)
        linarith only [ha, hb]
      have hm := mul_le_mul_of_nonneg_left hcosh2 hpos_r
      have hm2 := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-y ^ 2 * t)).le
      have hexp : Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * (Real.exp (2 * y * r * t) + Real.exp (-2 * y * r * t))) =
          Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (2 * y * r * t)) +
          Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * Real.exp (-2 * y * r * t)) := by ring
      linarith only [hm2, hexp]
    have hi2 := intervalIntegral.integral_mono_on hη0.le
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 η)
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 η) hpt2
    have hd2 : ∀ r : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-y ^ 2 * t) * (2 * (x ^ 3 * t / 3 - x ^ 5 * t ^ 2 / 10)))
        (Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * 2)) r := by
      intro r
      have h1 := ((hasDerivAt_pow 3 r).mul_const t).div_const 3
      have h2 := ((hasDerivAt_pow 5 r).mul_const (t ^ 2)).div_const 10
      refine (((h1.fun_sub h2).const_mul 2).const_mul (Real.exp (-y ^ 2 * t))).congr_deriv ?_
      norm_num; ring
    have hftc2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd2 r)
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 η)
    have hid_int : ∫ r in 0..η, Real.exp (-y ^ 2 * t) * ((r ^ 2 * t - r ^ 4 * t ^ 2 / 2) * 2) =
        ∫ r in 0..η, Real.exp (-y ^ 2 * t) * (2 * (r ^ 2 * t - r ^ 4 * t ^ 2 / 2)) := by
      refine intervalIntegral.integral_congr (fun r _ => by ring)
    rw [← hid_int, hftc2] at hi2
    have heval2 : Real.exp (-y ^ 2 * t) * (2 * (η ^ 3 * t / 3 - η ^ 5 * t ^ 2 / 10)) -
        Real.exp (-y ^ 2 * t) * (2 * ((0 : ℝ) ^ 3 * t / 3 - (0 : ℝ) ^ 5 * t ^ 2 / 10)) =
        (η ^ 2 / 3 - η ^ 4 * t / 10) * t * (2 * η * Real.exp (-y ^ 2 * t)) := by ring
    linarith only [hi2, heval2]
  have h1c : (1 + (2 * y * η * t) ^ 2 / 6 + (2 * y * η * t) ^ 4 / 100) * (2 * η * Real.exp (-y ^ 2 * t)) -
      (η ^ 2 / 3 - η ^ 4 * t / 10) * t * (2 * η * Real.exp (-y ^ 2 * t)) =
      (1 + (2 * y * η) ^ 2 * t ^ 2 / 6 + (2 * y * η) ^ 4 * t ^ 4 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) * t) *
        (2 * η * Real.exp (-y ^ 2 * t)) := by ring
  linarith only [hsh, hi, hint1, hint2, h1c]

private lemma gaussian_sum_ge_2b_p3_box {y η t E1 E2 K_hp M4 : ℝ} (hy : 1 / 4 ≤ y) (hη0 : 0 < η)
    (hη_le : η ≤ 1 / 4) (ht : 0 < t) (ht_ub : t ≤ 7 / 10) (h2b : 2 * (y - η) ^ 2 * t < 3)
    (hE1 : Real.exp ((2 * y - η) * η * t) ≤ E1) (hE2 : Real.exp (y ^ 2 * t) ≤ E2)
    (hK0 : 0 ≤ K_hp) (hK_bd : ∀ u ∈ Set.Icc (y - η) (y + η), 1 - 2 * u ^ 2 * t ≤ K_hp)
    (hM4 : ∀ u ∈ Set.Icc (y - η) (y + η), |4 * (u ^ 2 * t) ^ 2 - 12 * (u ^ 2 * t) + 3| ≤ M4)
    (hdiff : K_hp / 12 * E1 + 7 * M4 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
        (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 -
        (η ^ 2 / 3 - η ^ 4 * t / 10) ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η)) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by
  have hη12 : η < 1 / 2 := by linarith only [hη_le]
  rcases case2_tsum_reindex y η t hη0 hη12 ht with ⟨_, _, hreidx⟩
  rw [hreidx]
  have hp5 := P5_gauss_bounds y η t hη0 ht
  set A := (1 / 2 - η) * (2 * y - 1 / 2 + η) * t
  have hA_nn : 0 ≤ A := by
    have : 0 ≤ 1 / 2 - η := by linarith only [hη_le]
    have : 0 ≤ 2 * y - 1 / 2 + η := by linarith only [hy, hη0]
    dsimp [A]; positivity
  have hlhs_lb : (1 + ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
      ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
      ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) * t / (2 * η)) *
        (2 * η * Real.exp (-y ^ 2 * t)) ≤
      Real.exp (-(y - 1 / 2 + η) ^ 2 * t) - 2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) := by
    have hexp := exp_ge_poly3 hA_nn
    have h1 : A + A ^ 2 / 2 + A ^ 3 / 6 =
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) * t := by
      dsimp [A]; ring
    have heq_e : Real.exp A * Real.exp (-y ^ 2 * t) = Real.exp (-(y - 1 / 2 + η) ^ 2 * t) := by
      rw [← Real.exp_add]; congr 1; dsimp [A]; ring
    have hmul := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-y ^ 2 * t)).le
    have hcan : (1 + ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
        ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
        ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) * t / (2 * η)) *
          (2 * η * Real.exp (-y ^ 2 * t)) =
        (1 + A + A ^ 2 / 2 + A ^ 3 / 6) * Real.exp (-y ^ 2 * t) -
          2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) := by
      rw [← h1]; field_simp [hη0.ne']; ring
    linarith only [hmul, heq_e, hcan]
  have hx_le : 2 * y * η * t ≤ 3 / 5 := by
    by_cases hy127 : y ≤ 12 / 7
    · have h1 : 2 * y * η ≤ 2 * (12 / 7) * (1 / 4) := by nlinarith only [hy, hy127, hη0, hη_le]
      have hnn : 0 ≤ 2 * y * η := by positivity
      nlinarith only [h1, hnn, ht, ht_ub]
    · have hy_gt : 12 / 7 < y := lt_of_not_ge hy127
      have hy_sub : 41 / 28 ≤ y - η := by linarith only [hy_gt, hη_le]
      have hsq : 1681 * y ≤ 48 * 28 * (y - η) ^ 2 := by nlinarith only [hy_gt, hη_le, hy_sub]
      have hyt_bd : y * t ≤ 2016 / 1681 := by
        have : 1681 * (y * t) ≤ 2016 := by nlinarith only [hsq, h2b, ht]
        linarith only [this]
      nlinarith only [hyt_bd, hη0, hη_le]
  have hI_ub := gaussian_integral_ub_2b hy hη0 hη_le ht ht_ub hx_le
  have h1_exp : Real.exp (-(y - η) ^ 2 * t) ≤ E1 * Real.exp (-y ^ 2 * t) := by
    have heq : Real.exp (-(y - η) ^ 2 * t) = Real.exp ((2 * y - η) * η * t) * Real.exp (-y ^ 2 * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq]; exact mul_le_mul_of_nonneg_right hE1 (Real.exp_pos _).le
  have hE1_pos : 0 ≤ E1 := le_trans (Real.exp_pos _).le hE1
  have hp_ub : -2 * (y - η) * t * Real.exp (-(y - η) ^ 2 * t) +
      2 * (y + η) * t * Real.exp (-(y + η) ^ 2 * t) ≤
      (2 * K_hp * t * E1) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    let hu : ℝ → ℝ := fun u => u * Real.exp (-u ^ 2 * t)
    have hhu_der : ∀ u, HasDerivAt hu ((1 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t)) u := by
      intro u
      have harg : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
        (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
      exact ((hasDerivAt_id u).fun_mul harg.exp).congr_deriv (by simp; ring)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := hu) (a := y - η) (b := y + η)
      (fun u _ => hhu_der u) (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (y - η) (y + η))
    have hpt : ∀ u ∈ Set.Icc (y - η) (y + η),
        (1 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t) ≤ K_hp * Real.exp (-(y - η) ^ 2 * t) := by
      intro u hu_mem
      have hexp : Real.exp (-u ^ 2 * t) ≤ Real.exp (-(y - η) ^ 2 * t) := by
        apply Real.exp_le_exp.mpr
        have hyn : 0 ≤ y - η := by linarith only [hy, hη_le]
        have : (y - η) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hyn hu_mem.1 2
        nlinarith only [this, ht]
      have hK := hK_bd u hu_mem
      by_cases hneg : 0 ≤ 1 - 2 * u ^ 2 * t
      · exact mul_le_mul hK hexp (Real.exp_pos _).le hK0
      · have : (1 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hneg) (Real.exp_pos _).le
        exact le_trans this (mul_nonneg hK0 (Real.exp_pos _).le)
    have hi := intervalIntegral.integral_mono_on (by linarith only [hη0])
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (y - η) (y + η))
      (intervalIntegrable_const (μ := volume)) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    have hlen : (y + η) - (y - η) = 2 * η := by ring
    rw [hlen, hftc] at hi
    dsimp [hu] at hi
    have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * t)
    have hm2 := mul_le_mul_of_nonneg_left h1_exp (by positivity : 0 ≤ 2 * t * (K_hp * (2 * η)))
    linarith only [hm, hm2,
      show 2 * t * (K_hp * Real.exp (-(y - η) ^ 2 * t) * (2 * η)) =
        2 * t * (K_hp * (2 * η)) * Real.exp (-(y - η) ^ 2 * t) by ring,
      show 2 * t * (K_hp * (2 * η)) * (E1 * Real.exp (-y ^ 2 * t)) =
        (2 * K_hp * t * E1) * (2 * η * Real.exp (-y ^ 2 * t)) by ring]
  have hM4_nn : 0 ≤ M4 := le_trans (abs_nonneg _) (hM4 y ⟨by linarith only [hη0], by linarith only [hη0]⟩)
  have hh3_abs : |-4 * t ^ 2 * (y - η) * (2 * (y - η) ^ 2 * t - 3) * Real.exp (-(y - η) ^ 2 * t) -
      -4 * t ^ 2 * (y + η) * (2 * (y + η) ^ 2 * t - 3) * Real.exp (-(y + η) ^ 2 * t)| ≤
      (4 * M4 * t ^ 2 * E1) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have hraw := gaussian_f3_integral_abs_le (a := y - η) (b := y + η) (t := t) (M4 := M4)
      (E := Real.exp (-(y - η) ^ 2 * t)) (by linarith only [hη0]) ht.le hM4
      (fun u hu => by
        apply Real.exp_le_exp.mpr
        have hyn : 0 ≤ y - η := by linarith only [hy, hη_le]
        have hsq : (y - η) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hyn hu.1 2
        exact mul_le_mul_of_nonneg_right (neg_le_neg hsq) ht.le)
    have hM4_nn : 0 ≤ M4 := le_trans (abs_nonneg _) (hM4 y ⟨by linarith only [hη0], by linarith only [hη0]⟩)
    have hm := mul_le_mul_of_nonneg_left h1_exp (by positivity : 0 ≤ 4 * t ^ 2 * M4 * (2 * η))
    have heq1 : (y + η - (y - η)) * (4 * t ^ 2 * M4 * Real.exp (-(y - η) ^ 2 * t)) =
        4 * t ^ 2 * M4 * (2 * η) * Real.exp (-(y - η) ^ 2 * t) := by ring
    have heq2 : 4 * t ^ 2 * M4 * (2 * η) * (E1 * Real.exp (-y ^ 2 * t)) =
        (4 * M4 * t ^ 2 * E1) * (2 * η * Real.exp (-y ^ 2 * t)) := by ring
    exact le_trans hraw (heq1 ▸ heq2 ▸ hm)
  have hsqrt_le : Real.sqrt t ≤ 17 / 20 := by
    rw [Real.sqrt_le_iff]; refine ⟨by norm_num, by linarith only [ht_ub]⟩
  have herr_bd : 1 / 24 * (2 * η) * t ^ 2 * Real.sqrt t ≤
      (1 / 24 * t ^ 2 * (17 / 20) * E2) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have ht2η_nn : 0 ≤ 1 / 24 * (2 * η) * t ^ 2 := by positivity
    have h1 : 1 / 24 * (2 * η) * t ^ 2 * Real.sqrt t ≤ 1 / 24 * (2 * η) * t ^ 2 * (17 / 20) :=
      mul_le_mul_of_nonneg_left hsqrt_le ht2η_nn
    have h12 : 1 ≤ Real.exp (y ^ 2 * t) * Real.exp (-y ^ 2 * t) := by
      rw [← Real.exp_add, show y ^ 2 * t + -y ^ 2 * t = 0 by ring, Real.exp_zero]
    have hE2_prod : 1 ≤ E2 * Real.exp (-y ^ 2 * t) := by
      have hm := mul_le_mul_of_nonneg_right hE2 (Real.exp_pos (-y ^ 2 * t)).le
      linarith only [h12, hm]
    have hm2 := mul_le_mul_of_nonneg_left hE2_prod (by positivity : 0 ≤ 1 / 24 * (2 * η) * t ^ 2 * (17 / 20))
    linarith only [h1, hm2,
      show 1 / 24 * (2 * η) * t ^ 2 * (17 / 20) * (E2 * Real.exp (-y ^ 2 * t)) =
        (1 / 24 * t ^ 2 * (17 / 20) * E2) * (2 * η * Real.exp (-y ^ 2 * t)) by ring]
  have habs := (abs_le.mp hp5.2).2
  have hh3_neg := (abs_le.mp hh3_abs).1
  have hrhs_comb : (∑' m : ℕ, (Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) -
        Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t))) ≤
      (1 + (K_hp / 12 * E1 + 7 * M4 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
          (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 -
          (η ^ 2 / 3 - η ^ 4 * t / 10)) * t) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have hsum_le : ∑' m : ℕ, (Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) -
          Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t)) ≤
        (1 + (2 * y * η) ^ 2 * t ^ 2 / 6 + (2 * y * η) ^ 4 * t ^ 4 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) * t) *
            (2 * η * Real.exp (-y ^ 2 * t)) +
          1 / 24 * ((2 * K_hp * t * E1) * (2 * η * Real.exp (-y ^ 2 * t))) +
          7 / 5760 * ((4 * M4 * t ^ 2 * E1) * (2 * η * Real.exp (-y ^ 2 * t))) +
          (1 / 24 * t ^ 2 * (17 / 20) * E2) * (2 * η * Real.exp (-y ^ 2 * t)) := by
      linarith only [habs, hI_ub, hp_ub, hh3_neg, herr_bd]
    rw [show (1 + (2 * y * η) ^ 2 * t ^ 2 / 6 + (2 * y * η) ^ 4 * t ^ 4 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) * t) *
          (2 * η * Real.exp (-y ^ 2 * t)) +
        1 / 24 * ((2 * K_hp * t * E1) * (2 * η * Real.exp (-y ^ 2 * t))) +
        7 / 5760 * ((4 * M4 * t ^ 2 * E1) * (2 * η * Real.exp (-y ^ 2 * t))) +
        (1 / 24 * t ^ 2 * (17 / 20) * E2) * (2 * η * Real.exp (-y ^ 2 * t)) =
      (1 + (K_hp / 12 * E1 + 7 * M4 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
          (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 -
          (η ^ 2 / 3 - η ^ 4 * t / 10)) * t) * (2 * η * Real.exp (-y ^ 2 * t)) by ring] at hsum_le
    exact hsum_le
  have hmul_t := mul_le_mul_of_nonneg_right hdiff ht.le
  have hdiv_eq : ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
      ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
      ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) * t =
      ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
      ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
      ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) * t / (2 * η) := by ring
  have hcoef_le : 1 + (K_hp / 12 * E1 + 7 * M4 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
        (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 -
        (η ^ 2 / 3 - η ^ 4 * t / 10)) * t ≤
      1 + ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
        ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
        ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) * t / (2 * η) := by
    linarith only [hmul_t, hdiv_eq]
  have hmul_cmp := mul_le_mul_of_nonneg_right hcoef_le (by positivity : 0 ≤ 2 * η * Real.exp (-y ^ 2 * t))
  linarith only [hlhs_lb, hrhs_comb, hmul_cmp]

private lemma gaussian_sum_ge_2b_p3_hi {y η t : ℝ} (hy_gt12 : 1 / 2 < y) (hη0 : 0 < η)
    (hη_le : η ≤ 1 / 4) (ht : 0 < t) (ht_ub : t ≤ 7 / 10) (h2b : 2 * (y - η) ^ 2 * t < 3)
    (hM4_gen : ∀ u ∈ Set.Icc (y - η) (y + η), |4 * (u ^ 2 * t) ^ 2 - 12 * (u ^ 2 * t) + 3| ≤ 6)
    (hK_triv : ∀ u ∈ Set.Icc (y - η) (y + η), 1 - 2 * u ^ 2 * t ≤ (1 : ℝ))
    (hI_diff_clean : ∀ {E1 E2 : ℝ},
      1 / 12 * E1 + 7 * 6 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
        (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) →
      1 / 12 * E1 + 7 * 6 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
        (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η)) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by
  have hy : 1 / 4 ≤ y := by linarith only [hy_gt12]
  by_cases hy34 : y ≤ 3 / 4
  · have hE1 : Real.exp ((2 * y - η) * η * t) ≤ 4 / 3 := by
      have he1 : (2 * y - η) * η ≤ 3 / 8 :=
        le_trans (mul_le_mul (by linarith only [hy34, hη0] : 2 * y - η ≤ 3 / 2) hη_le hη0.le (by norm_num)) (by norm_num)
      have he : (2 * y - η) * η * t ≤ 21 / 80 :=
        le_trans (mul_le_mul he1 ht_ub ht.le (by norm_num)) (by norm_num)
      exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
    have hE2 : Real.exp (y ^ 2 * t) ≤ 3 / 2 := by
      have hy2 : y ^ 2 ≤ 9 / 16 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) hy34 2) (by norm_num)
      have he : y ^ 2 * t ≤ 63 / 160 :=
        le_trans (mul_le_mul hy2 ht_ub ht.le (by norm_num)) (by norm_num)
      exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
    refine gaussian_sum_ge_2b_p3_box hy hη0 hη_le ht ht_ub h2b hE1 hE2
      (K_hp := 1) (M4 := 6) (by norm_num) hK_triv hM4_gen (hI_diff_clean ?_)
    have hbase : 3 / 8 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) / (2 * η) := by
      rw [le_div_iff₀ (by linarith only [hη0])]
      have h1 : 1 / 2 + η ≤ 2 * y - 1 / 2 + η := by linarith only [hy_gt12]
      have h2 : (1 / 2 - η) * (1 / 2 + η) ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
        mul_le_mul_of_nonneg_left h1 (by linarith only [hη_le])
      have h3 : (1 / 4 : ℝ) - η ^ 2 = (1 / 2 - η) * (1 / 2 + η) := by ring
      have hη2 : η ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hη0.le hη_le 2) (by norm_num)
      linarith only [h2, h3, hη2, hη_le]
    have hrhs_ge : 3 / 8 ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) := by
      refine le_trans hbase (div_le_div_of_nonneg_right ?_ (by linarith only [hη0]))
      have h1 : 0 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
        mul_nonneg (by linarith only [hη_le]) (by linarith only [hy_gt12, hη0])
      have hsq : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) ht.le) zero_le_two
      have hcb : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6 :=
        div_nonneg (mul_nonneg (pow_nonneg h1 3) (sq_nonneg _)) (by norm_num)
      exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg le_rfl hsq) hcb
    have hxy_1 : 2 * y * η ≤ 3 / 8 :=
      le_trans (mul_le_mul (by linarith only [hy34] : 2 * y ≤ 3 / 2) hη_le hη0.le (by norm_num)) (by norm_num)
    have hxy_2 : (2 * y * η) ^ 2 ≤ (3 / 8) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith only [hy]) hη0.le) hxy_1 2
    have hxy_4 : (2 * y * η) ^ 4 ≤ (3 / 8) ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith only [hy]) hη0.le) hxy_1 4
    have ht3 : t ^ 3 ≤ (7 / 10) ^ 3 := pow_le_pow_left₀ ht.le ht_ub 3
    have ha : (2 * y * η) ^ 2 * t / 6 ≤ (3 / 8) ^ 2 * (7 / 10) / 6 :=
      div_le_div_of_nonneg_right (mul_le_mul hxy_2 ht_ub ht.le (by norm_num)) (by norm_num)
    have hb : (2 * y * η) ^ 4 * t ^ 3 / 100 ≤ (3 / 8) ^ 4 * (7 / 10) ^ 3 / 100 :=
      div_le_div_of_nonneg_right (mul_le_mul hxy_4 ht3 (pow_nonneg ht.le 3) (by norm_num)) (by norm_num)
    have htE1 : 7 * 6 / 1440 * t * (4 / 3 : ℝ) ≤ 7 * 6 / 1440 * (7 / 10) * (4 / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)
    have htE2 : 1 / 24 * t * (17 / 20) * (3 / 2 : ℝ) ≤ 1 / 24 * (7 / 10) * (17 / 20) * (3 / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)) (by norm_num)
    have hnum : (1 : ℝ) / 12 * (4 / 3) + 7 * 6 / 1440 * (7 / 10) * (4 / 3) + 1 / 24 * (7 / 10) * (17 / 20) * (3 / 2) +
        (3 / 8) ^ 2 * (7 / 10) / 6 + (3 / 8) ^ 4 * (7 / 10) ^ 3 / 100 ≤ 3 / 8 := by norm_num
    exact le_trans (add_le_add (add_le_add (add_le_add (add_le_add le_rfl htE1) htE2) ha) hb) (le_trans hnum hrhs_ge)
  · have hy_gt34 : 3 / 4 < y := lt_of_not_ge hy34
    by_cases hy54 : y ≤ 5 / 4
    · have hE1 : Real.exp ((2 * y - η) * η * t) ≤ 8 / 5 := by
        have he1 : (2 * y - η) * η ≤ 5 / 8 :=
          le_trans (mul_le_mul (by linarith only [hy54, hη0] : 2 * y - η ≤ 5 / 2) hη_le hη0.le (by norm_num)) (by norm_num)
        have he : (2 * y - η) * η * t ≤ 7 / 16 :=
          le_trans (mul_le_mul he1 ht_ub ht.le (by norm_num)) (by norm_num)
        exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
      have hE2 : Real.exp (y ^ 2 * t) ≤ 31 / 10 := by
        have hy2 : y ^ 2 ≤ 25 / 16 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) hy54 2) (by norm_num)
        have he : y ^ 2 * t / 2 ≤ 35 / 64 :=
          le_trans (div_le_div_of_nonneg_right (mul_le_mul hy2 ht_ub ht.le (by norm_num)) zero_le_two) (by norm_num)
        have hhalf : Real.exp (y ^ 2 * t / 2) ≤ 100 / 57 :=
          exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
        have hsq : Real.exp (y ^ 2 * t) = (Real.exp (y ^ 2 * t / 2)) ^ 2 := by
          rw [sq (Real.exp _), ← Real.exp_add]; congr 1; ring
        rw [hsq]
        exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le hhalf 2) (by norm_num)
      refine gaussian_sum_ge_2b_p3_box hy hη0 hη_le ht ht_ub h2b hE1 hE2
        (K_hp := 1) (M4 := 6) (by norm_num) hK_triv hM4_gen (hI_diff_clean ?_)
      have hbase : 5 / 8 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) / (2 * η) := by
        rw [le_div_iff₀ (by linarith only [hη0])]
        have h1 : 1 + η ≤ 2 * y - 1 / 2 + η := by linarith only [hy_gt34]
        have h2 : (1 / 2 - η) * (1 + η) ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
          mul_le_mul_of_nonneg_left h1 (by linarith only [hη_le])
        have h3 : (1 / 2 : ℝ) - η / 2 - η ^ 2 = (1 / 2 - η) * (1 + η) := by ring
        have hη2 : η ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hη0.le hη_le 2) (by norm_num)
        linarith only [h2, h3, hη2, hη_le]
      have hrhs_ge : 5 / 8 ≤
          ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
            ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
            ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) := by
        refine le_trans hbase (div_le_div_of_nonneg_right ?_ (by linarith only [hη0]))
        have h1 : 0 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
          mul_nonneg (by linarith only [hη_le]) (by linarith only [hy_gt34, hη0])
        have hsq : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 :=
          div_nonneg (mul_nonneg (sq_nonneg _) ht.le) zero_le_two
        have hcb : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6 :=
          div_nonneg (mul_nonneg (pow_nonneg h1 3) (sq_nonneg _)) (by norm_num)
        exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg le_rfl hsq) hcb
      have hxy_1 : 2 * y * η ≤ 5 / 8 :=
        le_trans (mul_le_mul (by linarith only [hy54] : 2 * y ≤ 5 / 2) hη_le hη0.le (by norm_num)) (by norm_num)
      have hxy_2 : (2 * y * η) ^ 2 ≤ (5 / 8) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by linarith only [hy]) hη0.le) hxy_1 2
      have hxy_4 : (2 * y * η) ^ 4 ≤ (5 / 8) ^ 4 :=
        pow_le_pow_left₀ (mul_nonneg (by linarith only [hy]) hη0.le) hxy_1 4
      have ht3 : t ^ 3 ≤ (7 / 10) ^ 3 := pow_le_pow_left₀ ht.le ht_ub 3
      have ha : (2 * y * η) ^ 2 * t / 6 ≤ (5 / 8) ^ 2 * (7 / 10) / 6 :=
        div_le_div_of_nonneg_right (mul_le_mul hxy_2 ht_ub ht.le (by norm_num)) (by norm_num)
      have hb : (2 * y * η) ^ 4 * t ^ 3 / 100 ≤ (5 / 8) ^ 4 * (7 / 10) ^ 3 / 100 :=
        div_le_div_of_nonneg_right (mul_le_mul hxy_4 ht3 (pow_nonneg ht.le 3) (by norm_num)) (by norm_num)
      have htE1 : 7 * 6 / 1440 * t * (8 / 5 : ℝ) ≤ 7 * 6 / 1440 * (7 / 10) * (8 / 5) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)
      have htE2 : 1 / 24 * t * (17 / 20) * (31 / 10 : ℝ) ≤ 1 / 24 * (7 / 10) * (17 / 20) * (31 / 10) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)) (by norm_num)
      have hnum : (1 : ℝ) / 12 * (8 / 5) + 7 * 6 / 1440 * (7 / 10) * (8 / 5) +
          1 / 24 * (7 / 10) * (17 / 20) * (31 / 10) +
          (5 / 8) ^ 2 * (7 / 10) / 6 + (5 / 8) ^ 4 * (7 / 10) ^ 3 / 100 ≤ 5 / 8 := by norm_num
      exact le_trans (add_le_add (add_le_add (add_le_add (add_le_add le_rfl htE1) htE2) ha) hb) (le_trans hnum hrhs_ge)
    · have hy_gt54 : 5 / 4 < y := lt_of_not_ge hy54
      have hE1 : Real.exp ((2 * y - η) * η * t) ≤ 2 := by
        have he : (2 * y - η) * η * t ≤ 3 / 5 := by
          by_cases hy127 : y ≤ 12 / 7
          · have h1 : 2 * y * η ≤ 6 / 7 :=
              le_trans (mul_le_mul (by linarith only [hy127] : 2 * y ≤ 24 / 7) hη_le hη0.le (by norm_num)) (by norm_num)
            have h2 : 2 * y * η * t ≤ 3 / 5 :=
              le_trans (mul_le_mul h1 ht_ub ht.le (by norm_num)) (by norm_num)
            have hη2t : 0 ≤ η ^ 2 * t := mul_nonneg (sq_nonneg η) ht.le
            linarith only [h2, hη2t, show (2 * y - η) * η * t = 2 * y * η * t - η ^ 2 * t by ring]
          · have hy_gt : 12 / 7 < y := lt_of_not_ge hy127
            have hy_sub : 41 / 28 ≤ y - η := by linarith only [hy_gt, hη_le]
            have hsq : 1681 * y ≤ 48 * 28 * (y - η) ^ 2 := by nlinarith only [hy_gt, hη_le, hy_sub]
            have hyt_bd : y * t ≤ 2016 / 1681 := by
              have : 1681 * (y * t) ≤ 2016 := by nlinarith only [hsq, h2b, ht]
              linarith only [this]
            have h2 : 2 * (y * t) * η ≤ 3 / 5 :=
              le_trans (mul_le_mul (by linarith only [hyt_bd] : 2 * (y * t) ≤ 4032 / 1681) hη_le hη0.le (by norm_num)) (by norm_num)
            have hη2t : 0 ≤ η ^ 2 * t := mul_nonneg (sq_nonneg η) ht.le
            linarith only [h2, hη2t, show (2 * y - η) * η * t = 2 * (y * t) * η - η ^ 2 * t by ring]
        exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
      have hE2 : Real.exp (y ^ 2 * t) ≤ 10 := by
        have he : y ^ 2 * t / 4 ≤ 11 / 20 := by
          by_cases hy74 : y ≤ 7 / 4
          · have hy2 : y ^ 2 ≤ 49 / 16 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) hy74 2) (by norm_num)
            exact le_trans (div_le_div_of_nonneg_right (mul_le_mul hy2 ht_ub ht.le (by norm_num)) (by norm_num)) (by norm_num)
          · have hy_gt : 7 / 4 < y := lt_of_not_ge hy74
            have hrat : 6 * y ≤ 7 * (y - η) := by linarith only [hy_gt, hη_le]
            have hsq : 36 * y ^ 2 ≤ 49 * (y - η) ^ 2 := by nlinarith only [hrat, hy_gt]
            have h1 : 36 * (y ^ 2 * t) ≤ 49 * ((y - η) ^ 2 * t) := by nlinarith only [hsq, ht]
            linarith only [h1, h2b]
        have hq : Real.exp (y ^ 2 * t / 4) ≤ 100 / 57 :=
          exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
        have h4 : Real.exp (y ^ 2 * t) = (Real.exp (y ^ 2 * t / 4)) ^ 4 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [h4]
        exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le hq 4) (by norm_num)
      refine gaussian_sum_ge_2b_p3_box hy hη0 hη_le ht ht_ub h2b hE1 hE2
        (K_hp := 1) (M4 := 6) (by norm_num) hK_triv hM4_gen (hI_diff_clean ?_)
      have hbase : 9 / 8 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) / (2 * η) := by
        rw [le_div_iff₀ (by linarith only [hη0])]
        have h1 : 2 + η ≤ 2 * y - 1 / 2 + η := by linarith only [hy_gt54]
        have h2 : (1 / 2 - η) * (2 + η) ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
          mul_le_mul_of_nonneg_left h1 (by linarith only [hη_le])
        have h3 : 1 - (3 / 2 : ℝ) * η - η ^ 2 = (1 / 2 - η) * (2 + η) := by ring
        have hη2 : η ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hη0.le hη_le 2) (by norm_num)
        linarith only [h2, h3, hη2, hη_le]
      have hrhs_ge : 9 / 8 ≤
          ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
            ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
            ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) := by
        refine le_trans hbase (div_le_div_of_nonneg_right ?_ (by linarith only [hη0]))
        have h1 : 0 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
          mul_nonneg (by linarith only [hη_le]) (by linarith only [hy_gt54, hη0])
        have hsq : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 :=
          div_nonneg (mul_nonneg (sq_nonneg _) ht.le) zero_le_two
        have hcb : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6 :=
          div_nonneg (mul_nonneg (pow_nonneg h1 3) (sq_nonneg _)) (by norm_num)
        exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg le_rfl hsq) hcb
      have hx_ub : 2 * y * η * t ≤ 3 / 5 := by
        by_cases hy127 : y ≤ 12 / 7
        · have h1 : 2 * y * η ≤ 6 / 7 :=
            le_trans (mul_le_mul (by linarith only [hy127] : 2 * y ≤ 24 / 7) hη_le hη0.le (by norm_num)) (by norm_num)
          exact le_trans (mul_le_mul h1 ht_ub ht.le (by norm_num)) (by norm_num)
        · have hy_gt : 12 / 7 < y := lt_of_not_ge hy127
          have hy_sub : 41 / 28 ≤ y - η := by linarith only [hy_gt, hη_le]
          have hsq : 1681 * y ≤ 48 * 28 * (y - η) ^ 2 := by nlinarith only [hy_gt, hη_le, hy_sub]
          have hyt_bd : y * t ≤ 2016 / 1681 := by
            have : 1681 * (y * t) ≤ 2016 := by nlinarith only [hsq, h2b, ht]
            linarith only [this]
          have h2 : 2 * (y * t) * η ≤ 3 / 5 :=
            le_trans (mul_le_mul (by linarith only [hyt_bd] : 2 * (y * t) ≤ 4032 / 1681) hη_le hη0.le (by norm_num)) (by norm_num)
          linarith only [h2, show 2 * y * η * t = 2 * (y * t) * η by ring]
      have hbd1 : (2 * y * η) ^ 2 * t ≤ 75 / 128 := by
        have hrat : 4 * y ≤ 5 * (y - η) := by linarith only [hy_gt54, hη_le]
        have hsq : 16 * y ^ 2 ≤ 25 * (y - η) ^ 2 := by nlinarith only [hrat, hy_gt54]
        have hη2 : η ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hη0.le hη_le 2) (by norm_num)
        have h1 : 16 * (y ^ 2 * t) ≤ 25 * ((y - η) ^ 2 * t) := by nlinarith only [hsq, ht]
        have hy2t : 4 * (y ^ 2 * t) ≤ 75 / 8 := by linarith only [h1, h2b]
        have hy2t_nn : 0 ≤ 4 * (y ^ 2 * t) := by positivity
        have heq : (2 * y * η) ^ 2 * t = 4 * (y ^ 2 * t) * η ^ 2 := by ring
        rw [heq]
        exact le_trans (mul_le_mul hy2t hη2 (sq_nonneg η) (by norm_num)) (by norm_num)
      have hbd2 : (2 * y * η) ^ 4 * t ^ 3 ≤ (75 / 128) * (3 / 5) ^ 2 := by
        have heq : (2 * y * η) ^ 4 * t ^ 3 = ((2 * y * η) ^ 2 * t) * (2 * y * η * t) ^ 2 := by ring
        have hx2 : (2 * y * η * t) ^ 2 ≤ (3 / 5) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by positivity) hη0.le) ht.le) hx_ub 2
        rw [heq]
        exact mul_le_mul hbd1 hx2 (sq_nonneg _) (by norm_num)
      have hxy : (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 ≤
          (75 / 128 : ℝ) / 6 + (75 / 128) * (3 / 5) ^ 2 / 100 :=
        add_le_add (div_le_div_of_nonneg_right hbd1 (by norm_num)) (div_le_div_of_nonneg_right hbd2 (by norm_num))
      have htE1 : 7 * 6 / 1440 * t * (2 : ℝ) ≤ 7 * 6 / 1440 * (7 / 10) * 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)
      have htE2 : 1 / 24 * t * (17 / 20) * (10 : ℝ) ≤ 1 / 24 * (7 / 10) * (17 / 20) * 10 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)) (by norm_num)
      have hnum : (1 : ℝ) / 12 * 2 + 7 * 6 / 1440 * (7 / 10) * 2 + 1 / 24 * (7 / 10) * (17 / 20) * 10 +
          ((75 / 128 : ℝ) / 6 + (75 / 128) * (3 / 5) ^ 2 / 100) ≤ 9 / 8 := by norm_num
      have hcomb : 1 / 12 * (2 : ℝ) + 7 * 6 / 1440 * t * 2 + 1 / 24 * t * (17 / 20) * 10 +
          (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 ≤ 9 / 8 := by
        linarith only [htE1, htE2, hxy, hnum]
      exact le_trans hcomb hrhs_ge

private lemma gaussian_sum_ge_2b_p3 {y η t : ℝ} (hy : 1 / 4 ≤ y) (hη0 : 0 < η)
    (hη_le : η ≤ 1 / 4) (ht : 0 < t) (ht_ub : t ≤ 7 / 10) (h2b : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by
  have hz_ub : ∀ u ∈ Set.Icc (y - η) (y + η), u ^ 2 * t ≤ 3 := by
    intro u hu
    have hu0 : 0 ≤ u := by linarith only [hy, hη_le, hu.1]
    have hu2 : u ^ 2 ≤ (y + η) ^ 2 := pow_le_pow_left₀ hu0 hu.2 2
    by_cases hy74 : y ≤ 7 / 4
    · have h1 : y + η ≤ 2 := by linarith only [hy74, hη_le]
      have h0 : 0 ≤ y + η := by linarith only [hy, hη0]
      have : (y + η) ^ 2 ≤ 4 := by nlinarith only [h0, h1]
      nlinarith only [hu2, this, ht, ht_ub]
    · have hy_gt : 7 / 4 < y := lt_of_not_ge hy74
      have hrat : 3 * (y + η) ≤ 4 * (y - η) := by linarith only [hy_gt, hη_le]
      have hsq : 9 * (y + η) ^ 2 ≤ 16 * (y - η) ^ 2 := by nlinarith only [hrat, hy_gt, hη0, hη_le]
      have : 9 * u ^ 2 * t ≤ 16 * ((y - η) ^ 2 * t) := by nlinarith only [hu2, hsq, ht]
      linarith only [this, h2b]
  have hM4_gen : ∀ u ∈ Set.Icc (y - η) (y + η), |4 * (u ^ 2 * t) ^ 2 - 12 * (u ^ 2 * t) + 3| ≤ 6 := by
    intro u hu
    have hz0 : 0 ≤ u ^ 2 * t := by positivity
    have hz1 := hz_ub u hu
    have hsq := sq_nonneg (2 * (u ^ 2 * t) - 3)
    rw [abs_le]; constructor <;> nlinarith only [hz0, hz1, hsq]
  have hK_triv : ∀ u ∈ Set.Icc (y - η) (y + η), 1 - 2 * u ^ 2 * t ≤ (1 : ℝ) := fun u _ => by
    nlinarith only [ht, sq_nonneg u]
  have hI_diff_clean : ∀ {E1 E2 : ℝ},
      1 / 12 * E1 + 7 * 6 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
        (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) →
      1 / 12 * E1 + 7 * 6 / 1440 * t * E1 + 1 / 24 * t * (17 / 20) * E2 +
        (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) := by
    intro E1 E2 hbase
    have hη2_nn : 0 ≤ η ^ 2 := by positivity
    have h1 : η ^ 4 * t / 10 ≤ η ^ 2 / 3 := by
      have : η ^ 2 * t ≤ 7 / 160 := by nlinarith only [hη0, hη_le, ht, ht_ub]
      nlinarith only [this, hη2_nn]
    linarith only [hbase, h1]
  by_cases hy38 : y ≤ 3 / 8
  · have hE1 : Real.exp ((2 * y - η) * η * t) ≤ 10 / 9 := by
      have he1 : (2 * y - η) * η ≤ y ^ 2 := by nlinarith only [sq_nonneg (y - η)]
      have hy2 : y ^ 2 ≤ 9 / 64 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) hy38 2) (by norm_num)
      have hy2t : y ^ 2 * t ≤ 63 / 640 := le_trans (mul_le_mul hy2 ht_ub ht.le (by norm_num)) (by norm_num)
      have he : (2 * y - η) * η * t ≤ 63 / 640 :=
        le_trans (mul_le_mul_of_nonneg_right he1 ht.le) hy2t
      exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
    have hE2 : Real.exp (y ^ 2 * t) ≤ 10 / 9 := by
      have hy2 : y ^ 2 ≤ 9 / 64 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) hy38 2) (by norm_num)
      have he : y ^ 2 * t ≤ 63 / 640 := le_trans (mul_le_mul hy2 ht_ub ht.le (by norm_num)) (by norm_num)
      exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
    refine gaussian_sum_ge_2b_p3_box hy hη0 hη_le ht ht_ub h2b hE1 hE2
      (K_hp := 1) (M4 := 3) (by norm_num) hK_triv
      (fun u hu => by
        have hz0 : 0 ≤ u ^ 2 * t := by positivity
        have hu2 : u ^ 2 ≤ (5 / 8 : ℝ) ^ 2 := by nlinarith only [hy, hy38, hη_le, hu.1, hu.2]
        have hz1 : u ^ 2 * t ≤ 35 / 128 := by nlinarith only [hu2, ht, ht_ub]
        have hsq := sq_nonneg (2 * (u ^ 2 * t) - 3)
        rw [abs_le]; constructor <;> nlinarith only [hz0, hz1, hsq]) ?_
    have hrhs_ge : 1 / 4 - η / 2 ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
          ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) := by
      have h0 : 0 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
        mul_nonneg (by linarith only [hη_le]) (by linarith only [hy, hη0])
      have hsq : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) ht.le) zero_le_two
      have hcb : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6 :=
        div_nonneg (mul_nonneg (pow_nonneg h0 3) (sq_nonneg _)) (by norm_num)
      have hlin : (1 / 2 - η) * η ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
        mul_le_mul_of_nonneg_left (by linarith only [hy] : η ≤ 2 * y - 1 / 2 + η) (by linarith only [hη_le])
      rw [le_div_iff₀ (by linarith only [hη0])]
      linarith only [hlin, hsq, hcb, show (1 / 4 - η / 2) * (2 * η) = (1 / 2 - η) * η by ring]
    have hmain : (1 : ℝ) / 12 * (10 / 9) + 7 * 3 / 1440 * t * (10 / 9) +
        1 / 24 * t * (17 / 20) * (10 / 9) +
        ((2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10)) ≤
        1 / 4 - η / 2 := by
      have h2y2 : (2 * y) ^ 2 ≤ 9 / 16 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) (by linarith only [hy38] : 2 * y ≤ 3 / 4) 2) (by norm_num)
      have h2y4 : (2 * y) ^ 4 ≤ 81 / 256 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) (by linarith only [hy38] : 2 * y ≤ 3 / 4) 4) (by norm_num)
      have hη2_nn : 0 ≤ η ^ 2 := sq_nonneg η
      have hη4_nn : 0 ≤ η ^ 4 := pow_nonneg hη0.le 4
      have ht3 : t ^ 3 ≤ (7 / 10) ^ 3 := pow_le_pow_left₀ ht.le ht_ub 3
      have h1 : (2 * y * η) ^ 2 * t / 6 ≤ (9 / 16 * (7 / 10) / 6) * η ^ 2 := by
        have h2yη2 : (2 * y * η) ^ 2 ≤ 9 / 16 * η ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right h2y2 hη2_nn
        have hmul := mul_le_mul h2yη2 ht_ub ht.le (by positivity)
        linarith only [hmul]
      have h2 : (2 * y * η) ^ 4 * t ^ 3 / 100 ≤ (81 / 256 * (7 / 10) ^ 3 / 100) * η ^ 4 := by
        have h4_bd : (2 * y * η) ^ 4 ≤ 81 / 256 * η ^ 4 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right h2y4 hη4_nn
        have hmul := mul_le_mul h4_bd ht3 (pow_nonneg ht.le 3) (by positivity)
        linarith only [hmul]
      have h3 : η ^ 4 * t / 10 ≤ (7 / 10 / 10) * η ^ 4 := by
        have := mul_le_mul_of_nonneg_left ht_ub hη4_nn
        linarith only [this]
      have hη2 : η ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hη0.le hη_le 2) (by norm_num)
      have h4 : η ^ 4 ≤ 1 / 16 * η ^ 2 := by
        have heq : η ^ 4 = η ^ 2 * η ^ 2 := by ring
        rw [heq]; exact mul_le_mul_of_nonneg_right hη2 hη2_nn
      have hq_eta : (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) ≤
          -((1 / 3 - 9 / 16 * (7 / 10) / 6 - 1 / 16 * (81 / 256 * (7 / 10) ^ 3 / 100 + 7 / 10 / 10)) * η ^ 2) := by
        have hc : (0 : ℝ) ≤ 81 / 256 * (7 / 10) ^ 3 / 100 + 7 / 10 / 10 := by norm_num
        have h4m := mul_le_mul_of_nonneg_left h4 hc
        linarith only [h1, h2, h3, h4m]
      have htA : 7 * 3 / 1440 * t * (10 / 9 : ℝ) ≤ 7 * 3 / 1440 * (7 / 10) * (10 / 9) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)
      have htB : 1 / 24 * t * (17 / 20) * (10 / 9 : ℝ) ≤ 1 / 24 * (7 / 10) * (17 / 20) * (10 / 9) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)) (by norm_num)
      by_cases hη15 : η ≤ 1 / 5
      · have hcpos : 0 ≤ (1 / 3 - 9 / 16 * (7 / 10) / 6 - 1 / 16 * (81 / 256 * (7 / 10) ^ 3 / 100 + 7 / 10 / 10) : ℝ) := by norm_num
        have hq0 : (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) ≤ 0 :=
          le_trans hq_eta (neg_nonpos.mpr (mul_nonneg hcpos hη2_nn))
        have hnum : (1 : ℝ) / 12 * (10 / 9) + 7 * 3 / 1440 * (7 / 10) * (10 / 9) +
            1 / 24 * (7 / 10) * (17 / 20) * (10 / 9) ≤ 1 / 4 - (1 / 5 : ℝ) / 2 := by norm_num
        linarith only [hq0, htA, htB, hη15, hnum]
      · have hη_gt15 : 1 / 5 < η := lt_of_not_ge hη15
        have hη2_lb : 1 / 25 ≤ η ^ 2 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hη_gt15.le 2)
        have hcpos : 0 ≤ (1 / 3 - 9 / 16 * (7 / 10) / 6 - 1 / 16 * (81 / 256 * (7 / 10) ^ 3 / 100 + 7 / 10 / 10) : ℝ) := by norm_num
        have hq_num : (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) ≤
            -((1 / 3 - 9 / 16 * (7 / 10) / 6 - 1 / 16 * (81 / 256 * (7 / 10) ^ 3 / 100 + 7 / 10 / 10)) * (1 / 25)) :=
          le_trans hq_eta (neg_le_neg (mul_le_mul_of_nonneg_left hη2_lb hcpos))
        have hnum : (1 : ℝ) / 12 * (10 / 9) + 7 * 3 / 1440 * (7 / 10) * (10 / 9) +
            1 / 24 * (7 / 10) * (17 / 20) * (10 / 9) -
            ((1 / 3 - 9 / 16 * (7 / 10) / 6 - 1 / 16 * (81 / 256 * (7 / 10) ^ 3 / 100 + 7 / 10 / 10)) * (1 / 25)) ≤
            1 / 4 - (1 / 4 : ℝ) / 2 := by norm_num
        linarith only [hq_num, htA, htB, hη_le, hnum]
    linarith only [hmain, hrhs_ge]
  · have hy_gt38 : 3 / 8 < y := lt_of_not_ge hy38
    by_cases hy12 : y ≤ 1 / 2
    · have hE1 : Real.exp ((2 * y - η) * η * t) ≤ 6 / 5 := by
        have he1 : (2 * y - η) * η ≤ 1 / 4 :=
          le_trans (mul_le_mul (by linarith only [hy12, hη0] : 2 * y - η ≤ 1) hη_le hη0.le zero_le_one) (by norm_num)
        have he : (2 * y - η) * η * t ≤ 7 / 40 :=
          le_trans (mul_le_mul he1 ht_ub ht.le (by norm_num)) (by norm_num)
        exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
      have hE2 : Real.exp (y ^ 2 * t) ≤ 6 / 5 := by
        have hy2 : y ^ 2 ≤ 1 / 4 := le_trans (pow_le_pow_left₀ (by linarith only [hy]) hy12 2) (by norm_num)
        have he : y ^ 2 * t ≤ 7 / 40 :=
          le_trans (mul_le_mul hy2 ht_ub ht.le (by norm_num)) (by norm_num)
        exact exp_ub_of_le (by norm_num) he (by norm_num) (by norm_num)
      refine gaussian_sum_ge_2b_p3_box hy hη0 hη_le ht ht_ub h2b hE1 hE2
        (K_hp := 1) (M4 := 3) (by norm_num) hK_triv
        (fun u hu => by
          have hz0 : 0 ≤ u ^ 2 * t := by positivity
          have hu2 : u ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by nlinarith only [hy_gt38, hy12, hη_le, hu.1, hu.2]
          have hz1 : u ^ 2 * t ≤ 1 / 2 := by nlinarith only [hu2, ht, ht_ub]
          rw [abs_le]; constructor <;> nlinarith only [hz0, hz1]) ?_
      have hrhs_ge : 1 / 4 ≤
          ((1 / 2 - η) * (2 * y - 1 / 2 + η) +
            ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 +
            ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6) / (2 * η) := by
        have h0 : 0 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
          mul_nonneg (by linarith only [hη_le]) (by linarith only [hy_gt38, hη0])
        have hsq : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 2 * t / 2 :=
          div_nonneg (mul_nonneg (sq_nonneg _) ht.le) zero_le_two
        have hcb : 0 ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η)) ^ 3 * t ^ 2 / 6 :=
          div_nonneg (mul_nonneg (pow_nonneg h0 3) (sq_nonneg _)) (by norm_num)
        have h1 : 1 / 4 + η ≤ 2 * y - 1 / 2 + η := by linarith only [hy_gt38]
        have h2 : (1 / 2 - η) * (1 / 4 + η) ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) :=
          mul_le_mul_of_nonneg_left h1 (by linarith only [hη_le])
        have hη2 : η ^ 2 ≤ 1 / 16 := le_trans (pow_le_pow_left₀ hη0.le hη_le 2) (by norm_num)
        have h3 : (1 / 8 : ℝ) + η / 4 - η ^ 2 = (1 / 2 - η) * (1 / 4 + η) := by ring
        have hlin : (1 / 4 : ℝ) * (2 * η) ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) := by
          linarith only [h2, h3, hη2, hη_le]
        rw [le_div_iff₀ (by linarith only [hη0])]
        linarith only [hlin, hsq, hcb]
      have h2yη : 2 * y * η ≤ 1 / 4 :=
        le_trans (mul_le_mul (by linarith only [hy12] : 2 * y ≤ 1) hη_le hη0.le zero_le_one) (by norm_num)
      have hsq : (2 * y * η) ^ 2 ≤ (1 / 4) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by linarith only [hy_gt38]) hη0.le) h2yη 2
      have h4 : (2 * y * η) ^ 4 ≤ (1 / 4) ^ 4 :=
        pow_le_pow_left₀ (mul_nonneg (by linarith only [hy_gt38]) hη0.le) h2yη 4
      have ht3 : t ^ 3 ≤ (7 / 10) ^ 3 := pow_le_pow_left₀ ht.le ht_ub 3
      have hη4 : η ^ 4 ≤ (1 / 4) ^ 4 := pow_le_pow_left₀ hη0.le hη_le 4
      have hη2_nn : 0 ≤ η ^ 2 := sq_nonneg η
      have h1 : (2 * y * η) ^ 2 * t / 6 ≤ (1 / 4) ^ 2 * (7 / 10) / 6 :=
        div_le_div_of_nonneg_right (mul_le_mul hsq ht_ub ht.le (by norm_num)) (by norm_num)
      have h2 : (2 * y * η) ^ 4 * t ^ 3 / 100 ≤ (1 / 4) ^ 4 * (7 / 10) ^ 3 / 100 :=
        div_le_div_of_nonneg_right (mul_le_mul h4 ht3 (pow_nonneg ht.le 3) (by norm_num)) (by norm_num)
      have h3 : η ^ 4 * t / 10 ≤ (1 / 4) ^ 4 * (7 / 10) / 10 :=
        div_le_div_of_nonneg_right (mul_le_mul hη4 ht_ub ht.le (by norm_num)) (by norm_num)
      have hxy : (2 * y * η) ^ 2 * t / 6 + (2 * y * η) ^ 4 * t ^ 3 / 100 - (η ^ 2 / 3 - η ^ 4 * t / 10) ≤
          (1 / 4 : ℝ) ^ 2 * (7 / 10) / 6 + (1 / 4) ^ 4 * (7 / 10) ^ 3 / 100 + (1 / 4) ^ 4 * (7 / 10) / 10 := by
        linarith only [h1, h2, h3, hη2_nn]
      have htA : 7 * 3 / 1440 * t * (6 / 5 : ℝ) ≤ 7 * 3 / 1440 * (7 / 10) * (6 / 5) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)
      have htB : 1 / 24 * t * (17 / 20) * (6 / 5 : ℝ) ≤ 1 / 24 * (7 / 10) * (17 / 20) * (6 / 5) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_ub (by norm_num)) (by norm_num)) (by norm_num)
      have hnum : (1 : ℝ) / 12 * (6 / 5) + 7 * 3 / 1440 * (7 / 10) * (6 / 5) +
          1 / 24 * (7 / 10) * (17 / 20) * (6 / 5) +
          ((1 / 4 : ℝ) ^ 2 * (7 / 10) / 6 + (1 / 4) ^ 4 * (7 / 10) ^ 3 / 100 + (1 / 4) ^ 4 * (7 / 10) / 10) ≤
          1 / 4 := by norm_num
      linarith only [hrhs_ge, hxy, htA, htB, hnum]
    · exact gaussian_sum_ge_2b_p3_hi (lt_of_not_ge hy12) hη0 hη_le ht ht_ub h2b hM4_gen hK_triv hI_diff_clean


lemma gaussian_sum_ge_2b_p3_aux {y η t : ℝ}
    (hy : 1 / 4 ≤ y) (hη0 : 0 < η) (hη_le : η ≤ 1 / 4) (ht : 0 < t)
    (ht_ub : t ≤ 7 / 10) (h2b : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) :=
  gaussian_sum_ge_2b_p3 hy hη0 hη_le ht ht_ub h2b

end SolGammaHelpers

theorem solution {y η t : ℝ}
    (hy : 1 / 4 ≤ y) (hη0 : 0 < η) (hη_le : η ≤ 1 / 4) (ht : 0 < t)
    (ht_ub : t ≤ 7 / 10) (h2b : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) :=
  SolGammaHelpers.gaussian_sum_ge_2b_p3_aux hy hη0 hη_le ht ht_ub h2b
