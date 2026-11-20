-- Prove2me | solution 1 for RademacherGamma_gaussian_sum_ge_c2_box
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:57:08.508373+00:00
-- url     : https://prove2.me/submissions/2e5d4268-cf45-4ca0-8bec-601002703248

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


private def okC2Step (m : ℕ) (y0 y1 t0 t1 e0 e1 : ℕ) : ℕ :=
  let w_hi := y1 + S_nat / 2 + m * S_nat
  let w_lo := y0 + S_nat / 2 + m * S_nat
  let e_lo := fmul (S_nat / 2 + m * S_nat - e1) (2 * y0 + S_nat / 2 + m * S_nat - e1)
  let u_lo := fmul (4 * fmul w_lo e0) t0
  let u2_lb := fmul u_lo u_lo
  let u2_ub := cmul u_lo u_lo
  let u3_lb := fmul u2_lb u_lo
  let u4_ub := cmul u2_ub u2_ub
  let pos := S_nat + (u2_ub + 5) / 6 + (u4_ub + 119) / 120
  let neg := u_lo / 2 + u3_lb / 24
  let p_alt := pos - neg
  let q_ub := min (cdiv S_nat (S_nat + u_lo / 2)) p_alt
  let et0 := fmul e_lo t0
  let et1 := cmul e_lo t1
  let um :=
    if et0 ≥ S_nat then cdiv t0 (expLb8Nat et0)
    else if et1 ≤ S_nat then cdiv t1 (expLb8Nat (fmul e_lo t1))
    else cdiv S_nat (fmul e_lo (expLb8Nat S_nat))
  let v2 := cmul (2 * w_hi) (cmul q_ub um)
  if e0 > 0 then
    let v1 := cdiv (cdiv S_nat (2 * e0)) (expLb8Nat et0)
    min v1 v2
  else v2

private def okC2Nat (y0 y1 t0 t1 e0 e1 : ℕ) : Bool :=
  if y0 ≥ e1 ∧ 2 * (y0 - e1) * (y0 - e1) * t0 ≥ 3 * S_nat * S_nat * S_nat then true
  else
    let g1 := fmul (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
    let a1 := fmul g1 t0
    let ratio_lb := fdiv g1 e1
    let r2 := fmul ratio_lb ratio_lb
    let r3 := fmul r2 ratio_lb
    let t02 := fmul t0 t0
    let t03 := fmul t02 t0
    let lhs := S_nat + fdiv a1 (2 * e1) + fmul (fmul r2 e0) t02 / 4 +
      fmul (fmul r3 (fmul e0 e0)) t03 / 12
    let e_tail := fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)
    let rhs := okC2Step 0 y0 y1 t0 t1 e0 e1 + okC2Step 1 y0 y1 t0 t1 e0 e1 +
      okC2Step 2 y0 y1 t0 t1 e0 e1 + cdiv S_nat (expLb8Nat (fmul e_tail t0))
    decide (lhs ≥ rhs)

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


private def c2Tree : BoxTree :=
  (.splitY 1025000000 (.splitT 2350000000 (.splitY 637500000 (.splitT 1525000000 (.splitY 443750000 (.splitT 1112500000 (.splitX 125000000 (.splitY 346875000 (.splitT 906250000 (.splitX 62500000 (.splitY 298437500 (.splitT 803125000 (.splitX 31250000 (.splitY 274218750 (.splitT 751562500 (.splitX 15625000 .leaf .leaf) (.splitX 15625000 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitT 751562500 (.splitX 46875000 .leaf .leaf) (.splitX 46875000 .leaf .leaf)) .leaf)) (.splitX 31250000 (.splitY 274218750 (.splitT 854687500 (.splitX 15625000 .leaf .leaf) .leaf) .leaf) (.splitY 274218750 (.splitT 854687500 (.splitX 46875000 .leaf .leaf) (.splitX 46875000 .leaf .leaf)) .leaf))) .leaf) (.splitY 298437500 (.splitT 803125000 (.splitX 93750000 (.splitY 274218750 (.splitT 751562500 (.splitX 78125000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf)) (.splitX 78125000 .leaf (.splitY 262109375 .leaf .leaf))) .leaf) (.splitY 274218750 (.splitT 751562500 (.splitX 109375000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 (.splitT 725781250 .leaf .leaf) .leaf)) (.splitX 109375000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf))) (.splitT 751562500 .leaf .leaf))) (.splitX 93750000 (.splitY 274218750 (.splitT 854687500 (.splitX 78125000 .leaf .leaf) (.splitX 78125000 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitT 854687500 (.splitX 109375000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf)) (.splitX 109375000 .leaf (.splitY 262109375 .leaf .leaf))) (.splitT 854687500 .leaf .leaf)))) (.splitT 803125000 (.splitX 93750000 .leaf (.splitY 322656250 .leaf .leaf)) (.splitX 93750000 .leaf .leaf)))) (.splitX 62500000 (.splitY 298437500 (.splitX 31250000 (.splitT 1009375000 (.splitY 274218750 (.splitX 15625000 .leaf .leaf) .leaf) (.splitY 274218750 (.splitX 15625000 .leaf .leaf) .leaf)) (.splitT 1009375000 (.splitY 274218750 (.splitX 46875000 .leaf (.splitT 957812500 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitX 46875000 .leaf .leaf) .leaf))) .leaf) (.splitY 298437500 (.splitX 93750000 (.splitT 1009375000 (.splitY 274218750 (.splitX 78125000 (.splitT 957812500 .leaf .leaf) (.splitT 957812500 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitX 78125000 .leaf .leaf) .leaf)) (.splitT 1009375000 (.splitY 274218750 (.splitX 109375000 (.splitT 957812500 .leaf .leaf) (.splitT 957812500 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitX 109375000 (.splitT 1060937500 .leaf .leaf) (.splitT 1060937500 .leaf .leaf)) .leaf))) (.splitX 93750000 .leaf (.splitT 1009375000 .leaf .leaf))))) (.splitT 906250000 (.splitX 62500000 .leaf (.splitT 803125000 (.splitY 395312500 .leaf .leaf) .leaf)) (.splitX 62500000 .leaf (.splitY 395312500 .leaf .leaf)))) (.splitY 346875000 (.splitT 906250000 (.splitX 187500000 (.splitY 298437500 (.splitT 803125000 (.splitX 156250000 (.splitY 274218750 (.splitT 751562500 (.splitX 140625000 (.splitY 262109375 (.splitT 725781250 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 725781250 .leaf .leaf) .leaf)) (.splitX 140625000 (.splitY 262109375 (.splitT 777343750 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 777343750 .leaf .leaf) .leaf))) (.splitT 751562500 (.splitX 140625000 .leaf .leaf) (.splitX 140625000 .leaf .leaf))) (.splitY 274218750 (.splitT 751562500 (.splitX 171875000 (.splitY 262109375 (.splitT 725781250 .leaf .leaf) (.splitT 725781250 .leaf .leaf)) (.splitY 262109375 (.splitT 725781250 (.splitX 179687500 .leaf .leaf) .leaf) (.splitT 725781250 .leaf .leaf))) (.splitX 171875000 (.splitY 262109375 (.splitT 777343750 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 777343750 .leaf .leaf) (.splitT 777343750 .leaf .leaf)))) (.splitT 751562500 (.splitX 171875000 .leaf (.splitY 286328125 .leaf .leaf)) (.splitX 171875000 .leaf .leaf)))) (.splitX 156250000 (.splitY 274218750 (.splitT 854687500 (.splitX 140625000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 (.splitT 828906250 .leaf .leaf) .leaf)) (.splitX 140625000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf))) (.splitT 854687500 .leaf .leaf)) (.splitY 274218750 (.splitT 854687500 (.splitX 171875000 (.splitY 262109375 (.splitT 828906250 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 828906250 .leaf .leaf) .leaf)) (.splitX 171875000 (.splitY 262109375 (.splitX 164062500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitX 179687500 .leaf .leaf) .leaf))) (.splitT 854687500 (.splitX 171875000 .leaf .leaf) (.splitX 171875000 .leaf .leaf))))) (.splitT 803125000 (.splitX 156250000 (.splitY 322656250 (.splitT 751562500 .leaf .leaf) .leaf) (.splitY 322656250 (.splitT 751562500 (.splitX 171875000 .leaf .leaf) .leaf) (.splitT 751562500 .leaf .leaf))) (.splitX 156250000 (.splitY 322656250 .leaf .leaf) (.splitY 322656250 (.splitT 854687500 .leaf .leaf) .leaf)))) (.splitY 298437500 (.splitT 803125000 (.splitX 218750000 (.splitY 274218750 (.splitT 751562500 (.splitX 203125000 (.splitY 262109375 (.splitT 725781250 (.splitX 195312500 .leaf .leaf) (.splitX 195312500 .leaf .leaf)) (.splitT 725781250 .leaf .leaf)) (.splitY 262109375 (.splitT 725781250 (.splitX 210937500 .leaf .leaf) (.splitX 210937500 .leaf .leaf)) (.splitT 725781250 .leaf .leaf))) (.splitX 203125000 (.splitY 262109375 (.splitT 777343750 (.splitX 195312500 .leaf .leaf) .leaf) (.splitT 777343750 .leaf .leaf)) (.splitY 262109375 (.splitT 777343750 (.splitX 210937500 .leaf .leaf) (.splitX 210937500 .leaf .leaf)) (.splitT 777343750 .leaf .leaf)))) (.splitT 751562500 (.splitX 203125000 (.splitY 286328125 (.splitT 725781250 .leaf .leaf) .leaf) (.splitY 286328125 (.splitT 725781250 .leaf .leaf) .leaf)) (.splitX 203125000 (.splitY 286328125 .leaf .leaf) (.splitY 286328125 (.splitT 777343750 .leaf .leaf) .leaf)))) (.splitY 274218750 (.splitT 751562500 (.splitX 234375000 (.splitY 262109375 (.splitT 725781250 (.splitX 226562500 (.splitY 256054687 .leaf .leaf) (.splitY 256054687 .leaf .leaf)) (.splitX 226562500 .leaf (.splitY 256054687 .leaf .leaf))) (.splitT 725781250 (.splitX 226562500 .leaf .leaf) (.splitX 226562500 .leaf .leaf))) (.splitY 262109375 (.splitT 725781250 (.splitX 242187500 (.splitY 256054687 .leaf .leaf) (.splitY 256054687 (.splitT 712890625 .leaf .leaf) .leaf)) (.splitX 242187500 (.splitY 256054687 .leaf .leaf) (.splitY 256054687 .leaf .leaf))) (.splitT 725781250 (.splitX 242187500 .leaf .leaf) (.splitX 242187500 .leaf .leaf)))) (.splitX 234375000 (.splitY 262109375 (.splitT 777343750 (.splitX 226562500 .leaf .leaf) (.splitX 226562500 .leaf .leaf)) (.splitT 777343750 .leaf .leaf)) (.splitY 262109375 (.splitT 777343750 (.splitX 242187500 (.splitY 256054687 .leaf .leaf) (.splitY 256054687 .leaf .leaf)) (.splitX 242187500 (.splitY 256054687 .leaf .leaf) (.splitY 256054687 .leaf .leaf))) (.splitT 777343750 (.splitX 242187500 .leaf .leaf) (.splitX 242187500 .leaf .leaf))))) (.splitT 751562500 (.splitX 234375000 (.splitY 286328125 (.splitT 725781250 .leaf .leaf) (.splitT 725781250 .leaf .leaf)) (.splitY 286328125 (.splitT 725781250 (.splitX 242187500 .leaf .leaf) .leaf) (.splitT 725781250 .leaf .leaf))) (.splitX 234375000 (.splitY 286328125 (.splitT 777343750 .leaf .leaf) .leaf) (.splitY 286328125 (.splitT 777343750 .leaf .leaf) (.splitT 777343750 .leaf .leaf)))))) (.splitX 218750000 (.splitY 274218750 (.splitT 854687500 (.splitX 203125000 (.splitY 262109375 (.splitT 828906250 .leaf .leaf) (.splitT 828906250 .leaf .leaf)) (.splitY 262109375 (.splitT 828906250 (.splitX 210937500 .leaf .leaf) (.splitX 210937500 .leaf .leaf)) (.splitT 828906250 .leaf .leaf))) (.splitX 203125000 (.splitY 262109375 (.splitX 195312500 .leaf (.splitT 880468750 .leaf .leaf)) .leaf) (.splitY 262109375 (.splitX 210937500 (.splitT 880468750 .leaf .leaf) (.splitT 880468750 .leaf .leaf)) (.splitX 210937500 .leaf .leaf)))) (.splitT 854687500 (.splitX 203125000 (.splitY 286328125 .leaf .leaf) (.splitY 286328125 .leaf .leaf)) (.splitX 203125000 .leaf (.splitY 286328125 .leaf .leaf)))) (.splitY 274218750 (.splitT 854687500 (.splitX 234375000 (.splitY 262109375 (.splitT 828906250 (.splitX 226562500 .leaf .leaf) (.splitX 226562500 .leaf .leaf)) (.splitT 828906250 .leaf .leaf)) (.splitY 262109375 (.splitT 828906250 (.splitX 242187500 .leaf (.splitY 256054687 .leaf .leaf)) (.splitX 242187500 .leaf (.splitY 256054687 .leaf .leaf))) (.splitT 828906250 (.splitX 242187500 .leaf .leaf) (.splitX 242187500 .leaf .leaf)))) (.splitX 234375000 (.splitY 262109375 (.splitX 226562500 (.splitT 880468750 .leaf .leaf) (.splitT 880468750 .leaf .leaf)) (.splitX 226562500 .leaf .leaf)) (.splitY 262109375 (.splitX 242187500 (.splitT 880468750 .leaf .leaf) (.splitT 880468750 .leaf .leaf)) (.splitX 242187500 (.splitT 880468750 .leaf .leaf) (.splitT 880468750 .leaf .leaf))))) (.splitT 854687500 (.splitX 234375000 (.splitY 286328125 (.splitT 828906250 .leaf .leaf) .leaf) (.splitY 286328125 (.splitT 828906250 .leaf .leaf) (.splitT 828906250 .leaf .leaf))) (.splitX 234375000 (.splitY 286328125 .leaf .leaf) (.splitY 286328125 (.splitX 242187500 .leaf .leaf) .leaf)))))) (.splitT 803125000 (.splitX 218750000 (.splitY 322656250 (.splitT 751562500 (.splitX 203125000 .leaf .leaf) (.splitX 203125000 .leaf .leaf)) (.splitT 751562500 .leaf .leaf)) (.splitY 322656250 (.splitT 751562500 (.splitX 234375000 (.splitY 310546875 .leaf .leaf) (.splitY 310546875 (.splitT 725781250 .leaf .leaf) .leaf)) (.splitX 234375000 (.splitY 310546875 .leaf .leaf) (.splitY 310546875 .leaf .leaf))) (.splitT 751562500 (.splitX 234375000 .leaf .leaf) (.splitX 234375000 .leaf .leaf)))) (.splitX 218750000 (.splitY 322656250 (.splitT 854687500 (.splitX 203125000 .leaf .leaf) (.splitX 203125000 .leaf .leaf)) (.splitT 854687500 .leaf .leaf)) (.splitY 322656250 (.splitT 854687500 (.splitX 234375000 .leaf (.splitY 310546875 .leaf .leaf)) (.splitX 234375000 .leaf .leaf)) (.splitT 854687500 (.splitX 234375000 .leaf .leaf) (.splitX 234375000 .leaf .leaf))))))) (.splitX 187500000 (.splitY 298437500 (.splitX 156250000 (.splitT 1009375000 (.splitY 274218750 (.splitX 140625000 (.splitT 957812500 (.splitY 262109375 .leaf .leaf) .leaf) (.splitT 957812500 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf))) (.splitX 140625000 .leaf .leaf)) (.splitY 274218750 (.splitX 140625000 (.splitT 1060937500 .leaf .leaf) (.splitT 1060937500 .leaf .leaf)) (.splitX 140625000 .leaf .leaf))) (.splitT 1009375000 (.splitY 274218750 (.splitX 171875000 (.splitT 957812500 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf)) (.splitT 957812500 (.splitY 262109375 (.splitX 179687500 .leaf .leaf) .leaf) (.splitY 262109375 .leaf .leaf))) (.splitX 171875000 (.splitT 957812500 .leaf .leaf) (.splitT 957812500 .leaf .leaf))) (.splitY 274218750 (.splitX 171875000 (.splitT 1060937500 (.splitY 262109375 .leaf .leaf) .leaf) (.splitT 1060937500 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf))) (.splitX 171875000 .leaf .leaf)))) (.splitX 156250000 (.splitT 1009375000 .leaf .leaf) (.splitT 1009375000 (.splitY 322656250 (.splitX 171875000 .leaf .leaf) .leaf) (.splitY 322656250 .leaf .leaf)))) (.splitY 298437500 (.splitX 218750000 (.splitT 1009375000 (.splitY 274218750 (.splitX 203125000 (.splitT 957812500 (.splitY 262109375 (.splitX 195312500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitX 195312500 .leaf .leaf) .leaf)) (.splitT 957812500 (.splitY 262109375 (.splitX 210937500 .leaf (.splitT 932031250 .leaf .leaf)) .leaf) (.splitY 262109375 (.splitX 210937500 .leaf .leaf) .leaf))) (.splitX 203125000 (.splitT 957812500 .leaf .leaf) (.splitT 957812500 .leaf .leaf))) (.splitY 274218750 (.splitX 203125000 (.splitT 1060937500 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf)) (.splitT 1060937500 (.splitY 262109375 (.splitX 210937500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitX 210937500 .leaf .leaf) .leaf))) (.splitX 203125000 (.splitT 1060937500 .leaf .leaf) (.splitT 1060937500 .leaf .leaf)))) (.splitT 1009375000 (.splitY 274218750 (.splitX 234375000 (.splitT 957812500 (.splitY 262109375 (.splitX 226562500 (.splitT 932031250 .leaf .leaf) (.splitT 932031250 .leaf .leaf)) (.splitX 226562500 .leaf .leaf)) (.splitY 262109375 (.splitX 226562500 (.splitT 983593750 .leaf .leaf) (.splitT 983593750 .leaf .leaf)) (.splitX 226562500 .leaf .leaf))) (.splitT 957812500 (.splitY 262109375 (.splitX 242187500 (.splitT 932031250 .leaf .leaf) (.splitT 932031250 .leaf .leaf)) (.splitX 242187500 .leaf (.splitT 932031250 .leaf .leaf))) (.splitY 262109375 (.splitX 242187500 (.splitT 983593750 .leaf .leaf) (.splitT 983593750 .leaf .leaf)) (.splitX 242187500 .leaf .leaf)))) (.splitX 234375000 (.splitT 957812500 (.splitY 286328125 .leaf .leaf) (.splitY 286328125 .leaf .leaf)) (.splitT 957812500 (.splitY 286328125 (.splitX 242187500 .leaf .leaf) .leaf) (.splitY 286328125 .leaf .leaf)))) (.splitY 274218750 (.splitX 234375000 (.splitT 1060937500 (.splitY 262109375 (.splitX 226562500 .leaf (.splitT 1035156250 .leaf .leaf)) .leaf) (.splitY 262109375 (.splitX 226562500 .leaf .leaf) .leaf)) (.splitT 1060937500 (.splitY 262109375 (.splitX 242187500 (.splitT 1035156250 .leaf .leaf) (.splitT 1035156250 .leaf .leaf)) (.splitX 242187500 .leaf .leaf)) (.splitY 262109375 (.splitX 242187500 (.splitT 1086718750 .leaf .leaf) (.splitT 1086718750 .leaf .leaf)) (.splitX 242187500 .leaf .leaf)))) (.splitX 234375000 (.splitT 1060937500 .leaf .leaf) (.splitT 1060937500 (.splitY 286328125 .leaf .leaf) (.splitY 286328125 .leaf .leaf)))))) (.splitX 218750000 (.splitT 1009375000 (.splitY 322656250 (.splitX 203125000 .leaf (.splitT 957812500 .leaf .leaf)) .leaf) (.splitY 322656250 (.splitX 203125000 .leaf .leaf) .leaf)) (.splitT 1009375000 (.splitY 322656250 (.splitX 234375000 (.splitT 957812500 .leaf .leaf) (.splitT 957812500 .leaf .leaf)) (.splitX 234375000 .leaf (.splitT 957812500 .leaf .leaf))) (.splitY 322656250 (.splitX 234375000 .leaf (.splitT 1060937500 .leaf .leaf)) (.splitX 234375000 .leaf .leaf))))))) (.splitT 906250000 (.splitX 187500000 (.splitT 803125000 (.splitY 395312500 (.splitX 156250000 .leaf (.splitT 751562500 .leaf .leaf)) (.splitX 156250000 .leaf .leaf)) (.splitY 395312500 (.splitX 156250000 .leaf .leaf) .leaf)) (.splitT 803125000 (.splitY 395312500 (.splitX 218750000 (.splitT 751562500 (.splitY 371093750 .leaf .leaf) .leaf) (.splitT 751562500 (.splitY 371093750 (.splitX 234375000 .leaf .leaf) .leaf) (.splitY 371093750 .leaf .leaf))) (.splitX 218750000 .leaf (.splitT 751562500 .leaf .leaf))) (.splitY 395312500 (.splitX 218750000 (.splitY 371093750 .leaf .leaf) (.splitY 371093750 (.splitT 854687500 .leaf .leaf) (.splitT 854687500 .leaf .leaf))) (.splitX 218750000 .leaf (.splitT 854687500 .leaf .leaf))))) (.splitX 187500000 (.splitY 395312500 (.splitX 156250000 .leaf (.splitT 1009375000 .leaf .leaf)) .leaf) (.splitY 395312500 (.splitX 218750000 (.splitT 1009375000 .leaf .leaf) (.splitT 1009375000 (.splitY 371093750 (.splitX 234375000 .leaf .leaf) .leaf) (.splitY 371093750 .leaf .leaf))) (.splitX 218750000 .leaf (.splitT 1009375000 .leaf .leaf))))))) (.splitX 125000000 (.splitY 346875000 (.splitX 62500000 (.splitY 298437500 (.splitT 1318750000 (.splitX 31250000 (.splitY 274218750 (.splitT 1215625000 .leaf .leaf) .leaf) (.splitY 274218750 (.splitT 1215625000 (.splitX 46875000 .leaf .leaf) .leaf) .leaf)) (.splitX 31250000 (.splitY 274218750 .leaf .leaf) (.splitY 274218750 (.splitT 1421875000 .leaf .leaf) .leaf))) .leaf) (.splitY 298437500 (.splitT 1318750000 (.splitX 93750000 (.splitY 274218750 (.splitT 1215625000 (.splitX 78125000 .leaf .leaf) (.splitX 78125000 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitT 1215625000 (.splitX 109375000 .leaf .leaf) (.splitX 109375000 .leaf .leaf)) .leaf)) (.splitX 93750000 (.splitY 274218750 (.splitT 1421875000 .leaf .leaf) .leaf) (.splitY 274218750 (.splitT 1421875000 (.splitX 109375000 .leaf .leaf) .leaf) .leaf))) (.splitT 1318750000 (.splitX 93750000 .leaf .leaf) .leaf))) (.splitX 62500000 .leaf .leaf)) (.splitY 346875000 (.splitX 187500000 (.splitY 298437500 (.splitT 1318750000 (.splitX 156250000 (.splitY 274218750 (.splitT 1215625000 (.splitX 140625000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf)) (.splitX 140625000 .leaf (.splitY 262109375 .leaf .leaf))) (.splitT 1215625000 .leaf .leaf)) (.splitY 274218750 (.splitT 1215625000 (.splitX 171875000 (.splitY 262109375 (.splitT 1164062500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 1164062500 .leaf .leaf) .leaf)) (.splitX 171875000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 (.splitT 1267187500 .leaf .leaf) .leaf))) (.splitT 1215625000 (.splitX 171875000 .leaf .leaf) .leaf))) (.splitX 156250000 (.splitY 274218750 (.splitT 1421875000 (.splitX 140625000 .leaf .leaf) (.splitX 140625000 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitT 1421875000 (.splitX 171875000 .leaf (.splitY 262109375 .leaf .leaf)) (.splitX 171875000 .leaf .leaf)) (.splitT 1421875000 .leaf .leaf)))) (.splitT 1318750000 (.splitX 156250000 (.splitT 1215625000 .leaf .leaf) (.splitT 1215625000 .leaf .leaf)) (.splitX 156250000 .leaf .leaf))) (.splitY 298437500 (.splitT 1318750000 (.splitX 218750000 (.splitY 274218750 (.splitT 1215625000 (.splitX 203125000 (.splitY 262109375 (.splitT 1164062500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 1164062500 .leaf .leaf) (.splitT 1164062500 .leaf .leaf))) (.splitX 203125000 (.splitY 262109375 (.splitT 1267187500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 1267187500 .leaf .leaf) .leaf))) (.splitT 1215625000 (.splitX 203125000 .leaf (.splitT 1164062500 .leaf .leaf)) (.splitX 203125000 .leaf .leaf))) (.splitY 274218750 (.splitT 1215625000 (.splitX 234375000 (.splitY 262109375 (.splitT 1164062500 (.splitX 226562500 .leaf .leaf) (.splitX 226562500 .leaf .leaf)) (.splitT 1164062500 .leaf .leaf)) (.splitY 262109375 (.splitT 1164062500 (.splitX 242187500 .leaf (.splitY 256054687 .leaf .leaf)) (.splitX 242187500 .leaf .leaf)) (.splitT 1164062500 .leaf .leaf))) (.splitX 234375000 (.splitY 262109375 (.splitT 1267187500 .leaf .leaf) (.splitT 1267187500 .leaf .leaf)) (.splitY 262109375 (.splitT 1267187500 (.splitX 242187500 .leaf .leaf) (.splitX 242187500 .leaf .leaf)) (.splitT 1267187500 .leaf .leaf)))) (.splitT 1215625000 (.splitX 234375000 (.splitT 1164062500 .leaf .leaf) (.splitT 1164062500 .leaf .leaf)) (.splitX 234375000 (.splitY 286328125 .leaf .leaf) (.splitY 286328125 (.splitT 1267187500 .leaf .leaf) .leaf))))) (.splitX 218750000 (.splitY 274218750 (.splitT 1421875000 (.splitX 203125000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 (.splitT 1370312500 .leaf .leaf) .leaf)) (.splitX 203125000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 .leaf .leaf))) (.splitT 1421875000 (.splitX 203125000 .leaf .leaf) .leaf)) (.splitY 274218750 (.splitT 1421875000 (.splitX 234375000 (.splitY 262109375 (.splitT 1370312500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 1370312500 (.splitX 242187500 .leaf .leaf) .leaf) (.splitT 1370312500 .leaf .leaf))) (.splitX 234375000 (.splitY 262109375 (.splitT 1473437500 .leaf .leaf) .leaf) (.splitY 262109375 (.splitT 1473437500 .leaf .leaf) .leaf))) (.splitT 1421875000 (.splitX 234375000 .leaf (.splitY 286328125 .leaf .leaf)) (.splitX 234375000 .leaf .leaf))))) (.splitT 1318750000 (.splitX 218750000 (.splitT 1215625000 (.splitY 322656250 .leaf .leaf) (.splitY 322656250 .leaf .leaf)) (.splitT 1215625000 (.splitY 322656250 (.splitX 234375000 .leaf .leaf) .leaf) (.splitY 322656250 (.splitX 234375000 .leaf .leaf) .leaf))) (.splitX 218750000 (.splitY 322656250 (.splitT 1421875000 .leaf .leaf) .leaf) (.splitY 322656250 (.splitT 1421875000 .leaf .leaf) (.splitT 1421875000 .leaf .leaf)))))) (.splitX 187500000 (.splitT 1318750000 (.splitY 395312500 (.splitX 156250000 .leaf .leaf) .leaf) (.splitY 395312500 .leaf .leaf)) (.splitT 1318750000 (.splitY 395312500 (.splitX 218750000 (.splitT 1215625000 .leaf .leaf) (.splitT 1215625000 .leaf .leaf)) (.splitX 218750000 .leaf .leaf)) (.splitY 395312500 (.splitX 218750000 .leaf .leaf) .leaf)))))) (.splitT 1112500000 (.splitX 125000000 (.splitT 906250000 (.splitX 62500000 .leaf .leaf) (.splitX 62500000 .leaf .leaf)) (.splitT 906250000 (.splitX 187500000 (.splitY 540625000 (.splitT 803125000 .leaf .leaf) .leaf) (.splitY 540625000 (.splitT 803125000 (.splitX 218750000 .leaf (.splitY 492187500 .leaf .leaf)) (.splitX 218750000 .leaf (.splitY 492187500 .leaf .leaf))) (.splitT 803125000 (.splitX 218750000 .leaf .leaf) .leaf))) (.splitX 187500000 (.splitY 540625000 .leaf .leaf) (.splitY 540625000 (.splitX 218750000 .leaf (.splitT 1009375000 .leaf .leaf)) (.splitX 218750000 .leaf .leaf))))) (.splitX 125000000 .leaf (.splitX 187500000 (.splitY 540625000 .leaf .leaf) (.splitY 540625000 (.splitT 1318750000 (.splitX 218750000 .leaf .leaf) .leaf) .leaf))))) (.splitY 443750000 (.splitX 125000000 (.splitY 346875000 (.splitT 1937500000 (.splitX 62500000 (.splitY 298437500 (.splitT 1731250000 (.splitX 31250000 .leaf .leaf) (.splitX 31250000 .leaf .leaf)) .leaf) (.splitY 298437500 (.splitT 1731250000 (.splitX 93750000 (.splitY 274218750 .leaf .leaf) (.splitY 274218750 (.splitT 1628125000 .leaf .leaf) .leaf)) (.splitX 93750000 .leaf (.splitY 274218750 .leaf .leaf))) .leaf)) (.splitX 62500000 (.splitY 298437500 (.splitX 31250000 .leaf .leaf) .leaf) (.splitY 298437500 (.splitX 93750000 .leaf .leaf) .leaf))) (.splitT 1937500000 (.splitX 62500000 .leaf .leaf) .leaf)) (.splitY 346875000 (.splitT 1937500000 (.splitX 187500000 (.splitY 298437500 (.splitT 1731250000 (.splitX 156250000 (.splitY 274218750 (.splitT 1628125000 .leaf .leaf) .leaf) (.splitY 274218750 (.splitT 1628125000 (.splitX 171875000 .leaf .leaf) (.splitX 171875000 .leaf .leaf)) .leaf)) (.splitX 156250000 (.splitY 274218750 .leaf .leaf) (.splitY 274218750 (.splitX 171875000 .leaf .leaf) .leaf))) (.splitT 1731250000 (.splitX 156250000 .leaf .leaf) .leaf)) (.splitY 298437500 (.splitT 1731250000 (.splitX 218750000 (.splitY 274218750 (.splitT 1628125000 (.splitX 203125000 .leaf (.splitY 262109375 .leaf .leaf)) (.splitX 203125000 .leaf .leaf)) (.splitT 1628125000 .leaf .leaf)) (.splitY 274218750 (.splitT 1628125000 (.splitX 234375000 (.splitY 262109375 .leaf .leaf) (.splitY 262109375 (.splitT 1576562500 .leaf .leaf) .leaf)) (.splitX 234375000 .leaf (.splitY 262109375 .leaf .leaf))) (.splitT 1628125000 (.splitX 234375000 .leaf .leaf) .leaf))) (.splitX 218750000 (.splitY 274218750 (.splitX 203125000 .leaf (.splitT 1834375000 .leaf .leaf)) .leaf) (.splitY 274218750 (.splitX 234375000 (.splitT 1834375000 .leaf .leaf) (.splitT 1834375000 .leaf .leaf)) (.splitX 234375000 .leaf .leaf)))) (.splitT 1731250000 (.splitX 218750000 .leaf (.splitY 322656250 (.splitT 1628125000 .leaf .leaf) .leaf)) (.splitX 218750000 .leaf .leaf)))) (.splitX 187500000 (.splitY 298437500 (.splitX 156250000 (.splitT 2143750000 .leaf .leaf) (.splitT 2143750000 (.splitY 274218750 .leaf .leaf) .leaf)) .leaf) (.splitY 298437500 (.splitX 218750000 (.splitT 2143750000 (.splitY 274218750 (.splitX 203125000 .leaf .leaf) .leaf) (.splitY 274218750 .leaf .leaf)) (.splitT 2143750000 (.splitY 274218750 (.splitX 234375000 .leaf .leaf) .leaf) (.splitY 274218750 (.splitX 234375000 .leaf .leaf) .leaf))) (.splitX 218750000 .leaf (.splitT 2143750000 .leaf .leaf))))) (.splitT 1937500000 (.splitX 187500000 (.splitY 395312500 .leaf .leaf) (.splitY 395312500 (.splitT 1731250000 (.splitX 218750000 .leaf .leaf) .leaf) .leaf)) (.splitX 187500000 .leaf (.splitY 395312500 .leaf .leaf))))) (.splitX 125000000 .leaf (.splitT 1937500000 (.splitX 187500000 .leaf (.splitY 540625000 .leaf .leaf)) (.splitX 187500000 .leaf .leaf))))) (.splitT 1525000000 (.splitT 1112500000 (.splitX 125000000 (.splitY 831250000 .leaf .leaf) (.splitY 831250000 (.splitT 906250000 (.splitX 187500000 .leaf (.splitY 734375000 (.splitT 803125000 .leaf .leaf) .leaf)) (.splitX 187500000 .leaf .leaf)) (.splitT 906250000 (.splitX 187500000 .leaf .leaf) .leaf))) (.splitX 125000000 .leaf (.splitY 831250000 (.splitX 187500000 .leaf .leaf) .leaf))) (.splitX 125000000 .leaf (.splitY 831250000 .leaf .leaf)))) (.splitY 637500000 (.splitY 443750000 (.splitX 125000000 (.splitY 346875000 (.splitT 3175000000 (.splitX 62500000 (.splitY 298437500 .leaf .leaf) (.splitY 298437500 (.splitT 2762500000 (.splitX 93750000 .leaf .leaf) .leaf) .leaf)) (.splitX 62500000 .leaf .leaf)) .leaf) (.splitY 346875000 (.splitT 3175000000 (.splitX 187500000 (.splitY 298437500 (.splitT 2762500000 (.splitX 156250000 .leaf .leaf) .leaf) .leaf) (.splitY 298437500 (.splitT 2762500000 (.splitX 218750000 (.splitY 274218750 .leaf .leaf) (.splitY 274218750 (.splitT 2556250000 .leaf .leaf) .leaf)) (.splitX 218750000 .leaf .leaf)) (.splitT 2762500000 .leaf .leaf))) (.splitX 187500000 .leaf (.splitY 298437500 (.splitT 3587500000 .leaf .leaf) .leaf))) (.splitT 3175000000 (.splitX 187500000 .leaf .leaf) .leaf))) (.splitX 125000000 .leaf .leaf)) (.splitX 125000000 .leaf .leaf))) (.splitT 2350000000 (.splitT 1525000000 (.splitT 1112500000 (.splitX 125000000 .leaf (.splitY 1412500000 (.splitT 906250000 (.splitX 187500000 .leaf .leaf) .leaf) .leaf)) (.splitX 125000000 .leaf .leaf)) (.splitX 125000000 .leaf .leaf)) .leaf))


private lemma c2_verified :
    verifyTree okC2Nat c2Tree (S_nat / 4) (18 * S_nat / 10) (7 * S_nat / 10) (4 * S_nat) 0 (S_nat / 4) = true := by
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

private lemma gaussian_convex_tail_sum_le {a₀ η t : ℝ} (haη : 0 ≤ a₀ - η) (_hη : 0 < η) (ht : 0 < t)
    (hcond : 3 ≤ 2 * (a₀ - η) ^ 2 * t)
    (hs : Summable (fun m : ℕ => Real.exp (-(a₀ + 1 / 2 + m - η) ^ 2 * t) -
      Real.exp (-(a₀ + 1 / 2 + m + η) ^ 2 * t))) :
    ∑' m : ℕ, (Real.exp (-(a₀ + 1 / 2 + m - η) ^ 2 * t) -
      Real.exp (-(a₀ + 1 / 2 + m + η) ^ 2 * t)) ≤ 2 * η * Real.exp (-(a₀ - η) ^ 2 * t) := by
  let f2 : ℝ → ℝ := fun u => 2 * t * (2 * u ^ 2 * t - 1) * Real.exp (-u ^ 2 * t)
  have hf2_ant : AntitoneOn f2 (Set.Ici (a₀ - η)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact (by dsimp [f2]; fun_prop : Continuous f2).continuousOn
    · intro u _
      have hp : HasDerivAt (fun x : ℝ => 2 * t * (2 * x ^ 2 * t - 1)) (8 * t ^ 2 * u) u := by
        have ha : HasDerivAt (fun x : ℝ => 2 * x ^ 2 * t - 1) (4 * u * t) u := by
          simpa using ((((hasDerivAt_pow 2 u).const_mul (2 : ℝ)).mul_const t).sub_const (1 : ℝ)).congr_deriv (by ring)
        exact (ha.const_mul (2 * t)).congr_deriv (by ring)
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (-2 * u * t * Real.exp (-u ^ 2 * t)) u := by
        have harg : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
          (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
        convert harg.exp using 1; ring
      exact (hp.fun_mul hexp).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici, Set.mem_Ioi] at hu
      have hp : HasDerivAt (fun x : ℝ => 2 * t * (2 * x ^ 2 * t - 1)) (8 * t ^ 2 * u) u := by
        have ha : HasDerivAt (fun x : ℝ => 2 * x ^ 2 * t - 1) (4 * u * t) u := by
          simpa using ((((hasDerivAt_pow 2 u).const_mul (2 : ℝ)).mul_const t).sub_const (1 : ℝ)).congr_deriv (by ring)
        exact (ha.const_mul (2 * t)).congr_deriv (by ring)
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * t)) (-2 * u * t * Real.exp (-u ^ 2 * t)) u := by
        have harg : HasDerivAt (fun x : ℝ => -x ^ 2 * t) (-2 * u * t) u :=
          (((hasDerivAt_pow 2 u).fun_neg).mul_const t).congr_deriv (by ring)
        convert harg.exp using 1; ring
      have hder := (hp.fun_mul hexp).congr_deriv (by
        show 8 * t ^ 2 * u * Real.exp (-u ^ 2 * t) +
          2 * t * (2 * u ^ 2 * t - 1) * (-2 * u * t * Real.exp (-u ^ 2 * t)) =
          4 * t ^ 2 * u * (3 - 2 * u ^ 2 * t) * Real.exp (-u ^ 2 * t)
        ring)
      rw [hder.deriv]
      have hu0 : 0 ≤ u := by linarith [haη, hu]
      have hu2 : (a₀ - η) ^ 2 ≤ u ^ 2 := by nlinarith only [haη, hu]
      have hle : 3 ≤ 2 * u ^ 2 * t := by nlinarith only [hu2, hcond, ht]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
        (Real.exp_pos _).le
  let h : ℝ → ℝ := fun w => Real.exp (-(w - η) ^ 2 * t) - Real.exp (-(w + η) ^ 2 * t)
  let h' : ℝ → ℝ := fun w =>
    -2 * (w - η) * t * Real.exp (-(w - η) ^ 2 * t) + 2 * (w + η) * t * Real.exp (-(w + η) ^ 2 * t)
  have hh_der : ∀ w, HasDerivAt h (h' w) w := by
    intro w
    have hid : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(x - η) ^ 2 * t))
        (-2 * (w - η) * t * Real.exp (-(w - η) ^ 2 * t)) w := by
      have hp : HasDerivAt (fun x : ℝ => -(x - η) ^ 2 * t) (-2 * (w - η) * t) w :=
        ((((hid.sub_const η).pow 2).neg).mul_const t).congr_deriv (by ring)
      convert hp.exp using 1; ring
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(x + η) ^ 2 * t))
        (-2 * (w + η) * t * Real.exp (-(w + η) ^ 2 * t)) w := by
      have hp : HasDerivAt (fun x : ℝ => -(x + η) ^ 2 * t) (-2 * (w + η) * t) w :=
        ((((hid.add_const η).pow 2).neg).mul_const t).congr_deriv (by ring)
      convert hp.exp using 1; ring
    exact (h1.fun_sub h2).congr_deriv (by dsimp [h']; ring)
  have hh'_mono : MonotoneOn h' (Set.Ici a₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a₀)
    · exact (by dsimp [h']; fun_prop : Continuous h').continuousOn
    · intro w _
      have hid : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
      have h1 : HasDerivAt (fun x : ℝ => -2 * (x - η) * t * Real.exp (-(x - η) ^ 2 * t))
          (f2 (w - η)) w := by
        have hl : HasDerivAt (fun x : ℝ => -2 * (x - η) * t) (-2 * t) w :=
          (((hid.sub_const η).const_mul (-2 : ℝ)).mul_const t).congr_deriv (by ring)
        have he : HasDerivAt (fun x : ℝ => Real.exp (-(x - η) ^ 2 * t))
            (-2 * (w - η) * t * Real.exp (-(w - η) ^ 2 * t)) w := by
          have hp : HasDerivAt (fun x : ℝ => -(x - η) ^ 2 * t) (-2 * (w - η) * t) w :=
            ((((hid.sub_const η).pow 2).neg).mul_const t).congr_deriv (by ring)
          convert hp.exp using 1; ring
        exact (hl.fun_mul he).congr_deriv (by dsimp [f2]; ring)
      have h2 : HasDerivAt (fun x : ℝ => 2 * (x + η) * t * Real.exp (-(x + η) ^ 2 * t))
          (-f2 (w + η)) w := by
        have hl : HasDerivAt (fun x : ℝ => 2 * (x + η) * t) (2 * t) w :=
          (((hid.add_const η).const_mul (2 : ℝ)).mul_const t).congr_deriv (by ring)
        have he : HasDerivAt (fun x : ℝ => Real.exp (-(x + η) ^ 2 * t))
            (-2 * (w + η) * t * Real.exp (-(w + η) ^ 2 * t)) w := by
          have hp : HasDerivAt (fun x : ℝ => -(x + η) ^ 2 * t) (-2 * (w + η) * t) w :=
            ((((hid.add_const η).pow 2).neg).mul_const t).congr_deriv (by ring)
          convert hp.exp using 1; ring
        exact (hl.fun_mul he).congr_deriv (by dsimp [f2]; ring)
      exact (h1.fun_add h2).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Ici, Set.mem_Ioi] at hw
      have hid : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
      have h1 : HasDerivAt (fun x : ℝ => -2 * (x - η) * t * Real.exp (-(x - η) ^ 2 * t))
          (f2 (w - η)) w := by
        have hl : HasDerivAt (fun x : ℝ => -2 * (x - η) * t) (-2 * t) w :=
          (((hid.sub_const η).const_mul (-2 : ℝ)).mul_const t).congr_deriv (by ring)
        have he : HasDerivAt (fun x : ℝ => Real.exp (-(x - η) ^ 2 * t))
            (-2 * (w - η) * t * Real.exp (-(w - η) ^ 2 * t)) w := by
          have hp : HasDerivAt (fun x : ℝ => -(x - η) ^ 2 * t) (-2 * (w - η) * t) w :=
            ((((hid.sub_const η).pow 2).neg).mul_const t).congr_deriv (by ring)
          convert hp.exp using 1; ring
        exact (hl.fun_mul he).congr_deriv (by dsimp [f2]; ring)
      have h2 : HasDerivAt (fun x : ℝ => 2 * (x + η) * t * Real.exp (-(x + η) ^ 2 * t))
          (-f2 (w + η)) w := by
        have hl : HasDerivAt (fun x : ℝ => 2 * (x + η) * t) (2 * t) w :=
          (((hid.add_const η).const_mul (2 : ℝ)).mul_const t).congr_deriv (by ring)
        have he : HasDerivAt (fun x : ℝ => Real.exp (-(x + η) ^ 2 * t))
            (-2 * (w + η) * t * Real.exp (-(w + η) ^ 2 * t)) w := by
          have hp : HasDerivAt (fun x : ℝ => -(x + η) ^ 2 * t) (-2 * (w + η) * t) w :=
            ((((hid.add_const η).pow 2).neg).mul_const t).congr_deriv (by ring)
          convert hp.exp using 1; ring
        exact (hl.fun_mul he).congr_deriv (by dsimp [f2]; ring)
      have hder := (h1.fun_add h2).congr_deriv (by rfl)
      rw [hder.deriv]
      have hcmp := hf2_ant (a := w - η) (b := w + η) (by simp only [Set.mem_Ici]; linarith)
        (by simp only [Set.mem_Ici]; linarith) (by linarith)
      linarith [hcmp]
  have hcont_h : Continuous h := by dsimp [h]; fun_prop
  have hstep : ∀ N : ℕ, ∑ m ∈ Finset.range N, h (a₀ + 1 / 2 + m) ≤ ∫ w in a₀..(a₀ + N), h w := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hadd : ∫ w in a₀..(a₀ + ((N + 1 : ℕ) : ℝ)), h w =
          (∫ w in a₀..(a₀ + N), h w) + ∫ w in (a₀ + N)..(a₀ + ((N + 1 : ℕ) : ℝ)), h w :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_h.intervalIntegrable _ _) (hcont_h.intervalIntegrable _ _)).symm
      have hcell : h (a₀ + 1 / 2 + N) ≤ ∫ w in (a₀ + N)..(a₀ + ((N + 1 : ℕ) : ℝ)), h w := by
        have hsymm : ∫ w in (a₀ + N)..(a₀ + ((N + 1 : ℕ) : ℝ)), h w =
            ∫ u in (-(1 / 2 : ℝ))..(1 / 2), h (a₀ + 1 / 2 + N + u) := by
          have := intervalIntegral.integral_comp_add_right h (a₀ + 1 / 2 + N) (a := -(1 / 2 : ℝ)) (b := 1 / 2)
          convert this.symm using 2 <;> (push_cast; ring)
        have havg : 2 * h (a₀ + 1 / 2 + N) ≤
            (∫ u in (-(1 / 2 : ℝ))..(1 / 2), h (a₀ + 1 / 2 + N + u)) +
            (∫ u in (-(1 / 2 : ℝ))..(1 / 2), h (a₀ + 1 / 2 + N - u)) := by
          rw [← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _)]
          have hpt : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
              2 * h (a₀ + 1 / 2 + N) ≤ h (a₀ + 1 / 2 + N + u) + h (a₀ + 1 / 2 + N - u) := by
            intro u hu
            have hmid : ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 2 →
                2 * h (a₀ + 1 / 2 + N) ≤ h (a₀ + 1 / 2 + N + v) + h (a₀ + 1 / 2 + N - v) := by
              intro v hv0 hv1
              rcases eq_or_lt_of_le hv0 with rfl | hv_pos
              · simp; linarith
              · have h1 := exists_hasDerivAt_eq_slope h h' (by linarith : a₀ + 1 / 2 + N - v < a₀ + 1 / 2 + N)
                  (hcont_h.continuousOn) (fun z _ => hh_der z)
                have h2 := exists_hasDerivAt_eq_slope h h' (by linarith : a₀ + 1 / 2 + N < a₀ + 1 / 2 + N + v)
                  (hcont_h.continuousOn) (fun z _ => hh_der z)
                rcases h1 with ⟨ξ₁, hξ₁, hslope₁⟩
                rcases h2 with ⟨ξ₂, hξ₂, hslope₂⟩
                have hden1 : a₀ + 1 / 2 + N - (a₀ + 1 / 2 + N - v) = v := by ring
                have hden2 : (a₀ + 1 / 2 + N + v) - (a₀ + 1 / 2 + N) = v := by ring
                rw [hden1, eq_div_iff hv_pos.ne'] at hslope₁
                rw [hden2, eq_div_iff hv_pos.ne'] at hslope₂
                have hmono := hh'_mono (a := ξ₁) (b := ξ₂) (by simp only [Set.mem_Ici]; linarith [hξ₁.1, hv1])
                  (by simp only [Set.mem_Ici]; linarith [hξ₁.1, hξ₁.2, hξ₂.1, hv1])
                  (by linarith [hξ₁.2, hξ₂.1])
                nlinarith only [hv_pos, hmono, hslope₁, hslope₂]
            by_cases hu0 : 0 ≤ u
            · exact hmid u hu0 hu.2
            · have := hmid (-u) (by linarith only [hu0]) (by linarith only [hu.1])
              convert this using 1; ring
          have hi := intervalIntegral.integral_mono_on (by norm_num)
            (intervalIntegrable_const (μ := volume))
            (Continuous.intervalIntegrable (μ := volume) (by fun_prop) _ _) hpt
          simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
          linarith only [hi]
        have hreflect : ∫ u in (-(1 / 2 : ℝ))..(1 / 2), h (a₀ + 1 / 2 + N - u) =
            ∫ u in (-(1 / 2 : ℝ))..(1 / 2), h (a₀ + 1 / 2 + N + u) := by
          have := intervalIntegral.integral_comp_neg (fun u : ℝ => h (a₀ + 1 / 2 + N + u))
            (a := -(1 / 2 : ℝ)) (b := 1 / 2)
          simpa only [sub_eq_add_neg, neg_neg] using this
        linarith only [hsymm, havg, hreflect]
      linarith only [ih, hadd, hcell]
  have hint_ub : ∀ N : ℕ, ∫ w in a₀..(a₀ + N), h w ≤ 2 * η * Real.exp (-(a₀ - η) ^ 2 * t) := by
    intro N
    have hcont_f : Continuous (fun v : ℝ => Real.exp (-v ^ 2 * t)) := by fun_prop
    have hsub : ∫ w in a₀..(a₀ + N), h w =
        (∫ w in a₀..(a₀ + N), Real.exp (-(w - η) ^ 2 * t)) -
        (∫ w in a₀..(a₀ + N), Real.exp (-(w + η) ^ 2 * t)) :=
      intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [hsub]
    have hl : ∫ w in a₀..(a₀ + N), Real.exp (-(w - η) ^ 2 * t) =
        ∫ v in (a₀ - η)..(a₀ + N - η), Real.exp (-v ^ 2 * t) := by
      simpa only [sub_eq_add_neg] using
        intervalIntegral.integral_comp_add_right (fun v : ℝ => Real.exp (-v ^ 2 * t)) (-η)
    have hr : ∫ w in a₀..(a₀ + N), Real.exp (-(w + η) ^ 2 * t) =
        ∫ v in (a₀ + η)..(a₀ + N + η), Real.exp (-v ^ 2 * t) :=
      intervalIntegral.integral_comp_add_right (fun v : ℝ => Real.exp (-v ^ 2 * t)) η
    rw [hl, hr]
    have hs1 : ∫ v in (a₀ - η)..(a₀ + N + η), Real.exp (-v ^ 2 * t) =
        (∫ v in (a₀ - η)..(a₀ + η), Real.exp (-v ^ 2 * t)) +
        ∫ v in (a₀ + η)..(a₀ + N + η), Real.exp (-v ^ 2 * t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)).symm
    have hs2 : ∫ v in (a₀ - η)..(a₀ + N + η), Real.exp (-v ^ 2 * t) =
        (∫ v in (a₀ - η)..(a₀ + N - η), Real.exp (-v ^ 2 * t)) +
        ∫ v in (a₀ + N - η)..(a₀ + N + η), Real.exp (-v ^ 2 * t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)).symm
    have htail_nn : 0 ≤ ∫ v in (a₀ + N - η)..(a₀ + N + η), Real.exp (-v ^ 2 * t) :=
      intervalIntegral.integral_nonneg (by linarith) fun v _ => (Real.exp_pos _).le
    have hpt : ∀ v ∈ Set.Icc (a₀ - η) (a₀ + η), Real.exp (-v ^ 2 * t) ≤ Real.exp (-(a₀ - η) ^ 2 * t) := by
      intro v hv
      have hsq : (a₀ - η) ^ 2 ≤ v ^ 2 := by nlinarith only [haη, hv.1]
      exact Real.exp_le_exp.mpr (by nlinarith only [hsq, ht])
    have hi := intervalIntegral.integral_mono_on (by linarith)
      (hcont_f.intervalIntegrable (μ := volume) _ _) (intervalIntegrable_const (μ := volume)) hpt
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    linarith [show a₀ + η - (a₀ - η) = 2 * η by ring]
  exact le_of_tendsto (Summable.hasSum hs).tendsto_sum_nat
    (Eventually.of_forall fun N => le_trans (hstep N) (hint_ub N))


private lemma okC2Step_v1_sound {m t0 e0 : ℕ} {e_lo : ℕ}
    (he0_pos : 0 < e0) (he_lo_r_pos : 0 < (e_lo : ℝ) / S_nat)
    {y t η : ℝ} (ht0 : (t0 : ℝ) / S_nat ≤ t) (he0 : (e0 : ℝ) / S_nat < η) (hη : 0 < η)
    (hexp_E_le : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) ≤
      Real.exp (-((e_lo : ℝ) / S_nat) * t)) :
    Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t) ≤
      ((cdiv (cdiv S_nat (2 * e0)) (expLb8Nat (fmul e_lo t0)) : ℕ) : ℝ) / S_nat *
        (2 * η * Real.exp (-y ^ 2 * t)) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  set et0 := fmul e_lo t0
  have hexp_eb : ((expLb8Nat et0 : ℕ) : ℝ) / S_nat ≤ Real.exp (((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) :=
    le_trans (expLb8Nat_le_exp et0) (Real.exp_le_exp.mpr (fmul_le e_lo t0))
  have hexp_pos : 0 < ((expLb8Nat et0 : ℕ) : ℝ) / S_nat := by
    have hlt : 0 < expLb8Nat et0 := lt_of_lt_of_le (by norm_num [S_nat] : 0 < S_nat) (expLb8Nat_ge_S et0)
    exact div_pos (Nat.cast_pos.mpr hlt) hS
  have het_mono : Real.exp (-((e_lo : ℝ) / S_nat) * t) ≤ Real.exp (-((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) :=
    Real.exp_le_exp.mpr (by nlinarith only [he_lo_r_pos, ht0])
  have hinv : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) ≤
      1 / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat) := by
    have h1 := le_trans hexp_E_le het_mono
    have h2 : Real.exp (-((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) ≤
        1 / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat) := by
      have heq : -((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) = -(((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) := by ring
      rw [heq, Real.exp_neg, one_div]
      exact inv_anti₀ hexp_pos hexp_eb
    exact le_trans h1 h2
  have he0_r_pos : 0 < 2 * ((e0 : ℝ) / S_nat) := by positivity
  have h2η : 1 / (2 * η) ≤ ((cdiv S_nat (2 * e0) : ℕ) : ℝ) / S_nat := by
    have h1 : 1 / (2 * η) ≤ (S_nat : ℝ) / (2 * e0 : ℕ) := by
      have hle_d : 2 * ((e0 : ℝ) / S_nat) ≤ 2 * η := by linarith only [he0]
      have hrew : (S_nat : ℝ) / (2 * e0 : ℕ) = 1 / (2 * ((e0 : ℝ) / S_nat)) := by push_cast; field_simp [hS.ne']
      rw [hrew, one_div, one_div]
      exact inv_anti₀ he0_r_pos hle_d
    exact le_trans h1 (le_cdiv S_nat (2 * e0) (by omega))
  have hmul_v1 : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) / (2 * η) ≤
      ((cdiv (cdiv S_nat (2 * e0)) (expLb8Nat et0) : ℕ) : ℝ) / S_nat := by
    have h1 : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) * (1 / (2 * η)) ≤
        (((cdiv S_nat (2 * e0) : ℕ) : ℝ) / S_nat) / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat) := by
      have ha := mul_le_mul h2η hinv (Real.exp_pos _).le (by positivity)
      have heq1 : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) * (1 / (2 * η)) =
          (1 / (2 * η)) * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) := by ring
      have heq2 : (((cdiv S_nat (2 * e0) : ℕ) : ℝ) / S_nat) / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat) =
          (((cdiv S_nat (2 * e0) : ℕ) : ℝ) / S_nat) * (1 / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat)) := by ring
      linarith only [ha, heq1, heq2]
    have h2 : (((cdiv S_nat (2 * e0) : ℕ) : ℝ) / S_nat) / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat) =
        ((cdiv S_nat (2 * e0) : ℕ) : ℝ) / ((expLb8Nat et0 : ℕ) : ℝ) := by field_simp [hS.ne']
    have h3 := le_cdiv (cdiv S_nat (2 * e0)) (expLb8Nat et0)
      (lt_of_lt_of_le (by norm_num [S_nat] : 0 < S_nat) (expLb8Nat_ge_S et0))
    have heq3 : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) / (2 * η) =
        Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) * (1 / (2 * η)) := by ring
    linarith only [h1, h2, h3, heq3]
  have hdiff_le : Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t) ≤
      Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) := by
    linarith only [Real.exp_pos (-(y + 1 / 2 + m + η) ^ 2 * t)]
  have hexp_eq : Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) =
      (Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) / (2 * η)) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have ha : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) * Real.exp (-y ^ 2 * t) =
        Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) := by rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t)
        = Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) * Real.exp (-y ^ 2 * t) := ha.symm
      _ = (Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) / (2 * η)) *
            (2 * η * Real.exp (-y ^ 2 * t)) := by field_simp [hη.ne']
  exact le_trans hdiff_le
    (le_trans (le_of_eq hexp_eq) (mul_le_mul_of_nonneg_right hmul_v1 (by positivity)))

private lemma okC2Step_sound {m y0 y1 t0 t1 e0 e1 : ℕ}
    (_hy01 : y0 ≤ y1) (_ht01 : t0 ≤ t1) (_he01 : e0 ≤ e1)
    (hy_lo : S_nat / 4 ≤ y0) (ht_lo : 7 * S_nat / 10 ≤ t0) (he_hi : e1 ≤ S_nat / 4)
    {y t η : ℝ} (hy0 : (y0 : ℝ) / S_nat ≤ y) (hy1 : y ≤ (y1 : ℝ) / S_nat)
    (ht0 : (t0 : ℝ) / S_nat ≤ t) (ht1 : t ≤ (t1 : ℝ) / S_nat)
    (he0 : (e0 : ℝ) / S_nat < η) (he1 : η ≤ (e1 : ℝ) / S_nat) :
    Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t) ≤
      ((okC2Step m y0 y1 t0 t1 e0 e1 : ℕ) : ℝ) / S_nat * (2 * η * Real.exp (-y ^ 2 * t)) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hy0_r_ge : (1 / 4 : ℝ) ≤ (y0 : ℝ) / S_nat := by
    have h1 : ((S_nat / 4 : ℕ) : ℝ) ≤ y0 := by exact_mod_cast hy_lo
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    have h3 := div_le_div_of_nonneg_right h1 hS.le
    linarith only [h2, h3]
  have he1_r_le : (e1 : ℝ) / S_nat ≤ 1 / 4 := by
    have h1 : (e1 : ℝ) ≤ ((S_nat / 4 : ℕ) : ℝ) := by exact_mod_cast he_hi
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    have h3 := div_le_div_of_nonneg_right h1 hS.le
    linarith only [h2, h3]
  have hη : 0 < η := lt_of_le_of_lt (by positivity) he0
  have ht : 0 < t := lt_of_lt_of_le (by
    have : 0 < t0 := by dsimp [S_nat] at ht_lo; omega
    positivity) ht0
  have hy_ge : 1 / 4 ≤ y := le_trans hy0_r_ge hy0
  have hη_le : η ≤ 1 / 4 := le_trans he1 he1_r_le
  set w_hi := y1 + S_nat / 2 + m * S_nat
  set w_lo := y0 + S_nat / 2 + m * S_nat
  set e_lo := fmul (S_nat / 2 + m * S_nat - e1) (2 * y0 + S_nat / 2 + m * S_nat - e1)
  set u_lo := fmul (4 * fmul w_lo e0) t0
  set u2_lb := fmul u_lo u_lo
  set u2_ub := cmul u_lo u_lo
  set u3_lb := fmul u2_lb u_lo
  set u4_ub := cmul u2_ub u2_ub
  set pos := S_nat + (u2_ub + 5) / 6 + (u4_ub + 119) / 120
  set neg := u_lo / 2 + u3_lb / 24
  set p_alt := pos - neg
  set q_ub := min (cdiv S_nat (S_nat + u_lo / 2)) p_alt
  set et0 := fmul e_lo t0
  set et1 := cmul e_lo t1
  set um :=
    if et0 ≥ S_nat then cdiv t0 (expLb8Nat et0)
    else if et1 ≤ S_nat then cdiv t1 (expLb8Nat (fmul e_lo t1))
    else cdiv S_nat (fmul e_lo (expLb8Nat S_nat))
  set v2 := cmul (2 * w_hi) (cmul q_ub um)
  have hw_lo_le : (w_lo : ℝ) / S_nat ≤ y + 1 / 2 + m := by
    have hcast : (w_lo : ℝ) / S_nat = (y0 : ℝ) / S_nat + 1 / 2 + m := by
      have hhalf : ((S_nat / 2 : ℕ) : ℝ) = (S_nat : ℝ) / 2 := by norm_num [S_nat]
      dsimp [w_lo]; push_cast; rw [hhalf]; field_simp
    linarith only [hcast, hy0]
  have hw_hi_ge : y + 1 / 2 + m ≤ (w_hi : ℝ) / S_nat := by
    have hcast : (w_hi : ℝ) / S_nat = (y1 : ℝ) / S_nat + 1 / 2 + m := by
      have hhalf : ((S_nat / 2 : ℕ) : ℝ) = (S_nat : ℝ) / 2 := by norm_num [S_nat]
      dsimp [w_hi]; push_cast; rw [hhalf]; field_simp
    linarith only [hcast, hy1]
  have he_lo_pos : 0 < e_lo := by
    have h1 : S_nat / 4 ≤ S_nat / 2 + m * S_nat - e1 := by dsimp [S_nat] at *; omega
    have h2 : S_nat / 4 ≤ 2 * y0 + S_nat / 2 + m * S_nat - e1 := by dsimp [S_nat] at *; omega
    have : (S_nat / 4) * (S_nat / 4) ≤ (S_nat / 2 + m * S_nat - e1) * (2 * y0 + S_nat / 2 + m * S_nat - e1) :=
      Nat.mul_le_mul h1 h2
    dsimp [e_lo, fmul]
    rw [Nat.div_pos_iff]
    exact ⟨by norm_num [S_nat], by dsimp [S_nat] at this ⊢; omega⟩
  have he_lo_r_pos : 0 < (e_lo : ℝ) / S_nat := div_pos (by exact_mod_cast he_lo_pos) hS
  have he_lo_le : (e_lo : ℝ) / S_nat ≤ (1 / 2 + m - η) * (2 * y + 1 / 2 + m - η) := by
    have hsub1 : e1 ≤ S_nat / 2 + m * S_nat := by dsimp [S_nat] at *; omega
    have hsub2 : e1 ≤ 2 * y0 + S_nat / 2 + m * S_nat := by dsimp [S_nat] at *; omega
    have hfm := fmul_le (S_nat / 2 + m * S_nat - e1) (2 * y0 + S_nat / 2 + m * S_nat - e1)
    have hhalf : ((S_nat / 2 : ℕ) : ℝ) = (S_nat : ℝ) / 2 := by norm_num [S_nat]
    have ha_eq : ((S_nat / 2 + m * S_nat - e1 : ℕ) : ℝ) / S_nat = 1 / 2 + m - (e1 : ℝ) / S_nat := by
      rw [Nat.cast_sub hsub1]; push_cast; rw [hhalf]; field_simp
    have ha : ((S_nat / 2 + m * S_nat - e1 : ℕ) : ℝ) / S_nat ≤ 1 / 2 + m - η := by
      linarith only [ha_eq, he1]
    have hb_eq : ((2 * y0 + S_nat / 2 + m * S_nat - e1 : ℕ) : ℝ) / S_nat =
        2 * ((y0 : ℝ) / S_nat) + 1 / 2 + m - (e1 : ℝ) / S_nat := by
      rw [Nat.cast_sub hsub2]; push_cast; rw [hhalf]; field_simp
    have hb : ((2 * y0 + S_nat / 2 + m * S_nat - e1 : ℕ) : ℝ) / S_nat ≤ 2 * y + 1 / 2 + m - η := by
      linarith only [hb_eq, hy0, he1]
    exact le_trans hfm (mul_le_mul ha hb (by positivity) (by linarith only [hη_le]))
  have hexp_E_le : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) ≤
      Real.exp (-((e_lo : ℝ) / S_nat) * t) := by
    apply Real.exp_le_exp.mpr
    have hfac : (y + 1 / 2 + m - η) ^ 2 - y ^ 2 = (1 / 2 + m - η) * (2 * y + 1 / 2 + m - η) := by ring
    rw [hfac]
    nlinarith only [he_lo_le, ht]
  -- Bound (1 - exp (-4*(y+1/2+m)*η*t)) / (4*(y+1/2+m)*η*t) ≤ q_ub / S_nat
  set u_true := 4 * (y + 1 / 2 + m) * η * t
  have hu_true_pos : 0 < u_true := by positivity
  have hu_lo_le : (u_lo : ℝ) / S_nat ≤ u_true := by
    have h1 := fmul_le (4 * fmul w_lo e0) t0
    have h2 := fmul_le w_lo e0
    have h3 : ((4 * fmul w_lo e0 : ℕ) : ℝ) / S_nat ≤ 4 * (y + 1 / 2 + m) * η := by
      have hcast : ((4 * fmul w_lo e0 : ℕ) : ℝ) / S_nat = 4 * (((fmul w_lo e0 : ℕ) : ℝ) / S_nat) := by
        push_cast; ring
      have hm := mul_le_mul hw_lo_le he0.le (by positivity) (by linarith only [hy_ge])
      rw [hcast]; linarith only [h2, hm]
    have hm2 := mul_le_mul h3 ht0 (by positivity) (by positivity)
    dsimp [u_true]; linarith only [h1, hm2]
  have hq_bound : (1 - Real.exp (-u_true)) / u_true ≤ (q_ub : ℝ) / S_nat := by
    have hq_cast : (q_ub : ℝ) / S_nat =
        min (((cdiv S_nat (S_nat + u_lo / 2) : ℕ) : ℝ) / S_nat) ((p_alt : ℝ) / S_nat) := by
      dsimp [q_ub]; push_cast
      rw [min_div_div_right hS.le]
    rw [hq_cast]
    refine le_min ?_ ?_
    · have h1 := one_sub_exp_neg_le_half hu_true_pos.le
      have h2 : (1 - Real.exp (-u_true)) / u_true ≤ 1 / (1 + u_true / 2) := by
        rw [div_le_iff₀ hu_true_pos]
        have heq : (1 / (1 + u_true / 2)) * u_true = u_true / (1 + u_true / 2) := by ring
        linarith only [h1, heq]
      have h3 : 1 / (1 + u_true / 2) ≤ 1 / (1 + ((u_lo : ℝ) / S_nat) / 2) := by
        rw [one_div, one_div]
        exact inv_anti₀ (by positivity) (by linarith only [hu_lo_le])
      have hd2 : ((u_lo / 2 : ℕ) : ℝ) ≤ (u_lo : ℝ) / 2 := by
        have : (u_lo / 2 : ℕ) * 2 ≤ u_lo := Nat.div_mul_le_self _ _
        have hcast : ((u_lo / 2 : ℕ) : ℝ) * 2 ≤ u_lo := by exact_mod_cast this
        linarith only [hcast]
      have hden_le : ((S_nat + u_lo / 2 : ℕ) : ℝ) / S_nat ≤ 1 + ((u_lo : ℝ) / S_nat) / 2 := by
        have hcast : ((S_nat + u_lo / 2 : ℕ) : ℝ) / S_nat = 1 + ((u_lo / 2 : ℕ) : ℝ) / S_nat := by
          push_cast; field_simp
        have hdiv := div_le_div_of_nonneg_right hd2 hS.le
        have hdiv2 : ((u_lo : ℝ) / 2) / S_nat = ((u_lo : ℝ) / S_nat) / 2 := by ring
        linarith only [hcast, hdiv, hdiv2]
      have hden_pos : 0 < S_nat + u_lo / 2 := by dsimp [S_nat]; omega
      have h4 := le_cdiv S_nat (S_nat + u_lo / 2) hden_pos
      have h5 : 1 / (1 + ((u_lo : ℝ) / S_nat) / 2) ≤ (S_nat : ℝ) / ((S_nat + u_lo / 2 : ℕ) : ℝ) := by
        have hpos1 : (0 : ℝ) < ((S_nat + u_lo / 2 : ℕ) : ℝ) / S_nat := by positivity
        rw [show (S_nat : ℝ) / ((S_nat + u_lo / 2 : ℕ) : ℝ) =
          (((S_nat + u_lo / 2 : ℕ) : ℝ) / S_nat)⁻¹ by field_simp, one_div]
        exact inv_anti₀ hpos1 hden_le
      exact le_trans h2 (le_trans h3 (le_trans h5 h4))
    · have hpoly : (1 - Real.exp (-u_true)) / u_true ≤
          1 - ((u_lo : ℝ) / S_nat) / 2 + ((u_lo : ℝ) / S_nat) ^ 2 / 6 -
          ((u_lo : ℝ) / S_nat) ^ 3 / 24 + ((u_lo : ℝ) / S_nat) ^ 4 / 120 := by
        by_cases hu0 : u_lo = 0
        · simp only [hu0, Nat.cast_zero, zero_div, zero_pow (by norm_num : 2 ≠ 0),
            zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 4 ≠ 0), sub_zero, add_zero]
          rw [div_le_one hu_true_pos]
          have hexp1 := Real.add_one_le_exp (-u_true)
          linarith only [hexp1]
        · have hu_pos : 0 < (u_lo : ℝ) / S_nat := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hu0)) hS
          have hant := one_sub_exp_neg_div_antitone hu_pos hu_true_pos hu_lo_le
          exact le_trans hant (one_sub_exp_neg_div_le_poly4 hu_pos)
      have hu2_lb : (u2_lb : ℝ) / S_nat ≤ ((u_lo : ℝ) / S_nat) ^ 2 := by
        have hfm := fmul_le u_lo u_lo
        have hsq := sq ((u_lo : ℝ) / S_nat)
        linarith only [hfm, hsq]
      have hu2_ub : ((u_lo : ℝ) / S_nat) ^ 2 ≤ (u2_ub : ℝ) / S_nat := by
        have hcm := le_cmul u_lo u_lo
        have hsq := sq ((u_lo : ℝ) / S_nat)
        linarith only [hcm, hsq]
      have hu3_lb : (u3_lb : ℝ) / S_nat ≤ ((u_lo : ℝ) / S_nat) ^ 3 := by
        have h1 := fmul_le u2_lb u_lo
        have h2 := mul_le_mul_of_nonneg_right hu2_lb (div_nonneg (Nat.cast_nonneg u_lo) hS.le)
        have hcube : ((u_lo : ℝ) / S_nat) ^ 2 * ((u_lo : ℝ) / S_nat) = ((u_lo : ℝ) / S_nat) ^ 3 := by ring
        linarith only [h1, h2, hcube]
      have hu4_ub : ((u_lo : ℝ) / S_nat) ^ 4 ≤ (u4_ub : ℝ) / S_nat := by
        have h1 := le_cmul u2_ub u2_ub
        have h2 : (((u_lo : ℝ) / S_nat) ^ 2) ^ 2 ≤ ((u2_ub : ℝ) / S_nat) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hu2_ub 2
        have hpow4 : (((u_lo : ℝ) / S_nat) ^ 2) ^ 2 = ((u_lo : ℝ) / S_nat) ^ 4 := by ring
        have hsq := sq ((u2_ub : ℝ) / S_nat)
        linarith only [h1, h2, hpow4, hsq]
      have hd2 : ((u_lo / 2 : ℕ) : ℝ) ≤ (u_lo : ℝ) / 2 := by
        have : (u_lo / 2 : ℕ) * 2 ≤ u_lo := Nat.div_mul_le_self _ _
        have hcast : ((u_lo / 2 : ℕ) : ℝ) * 2 ≤ u_lo := by exact_mod_cast this
        linarith only [hcast]
      have hd24 : ((u3_lb / 24 : ℕ) : ℝ) ≤ (u3_lb : ℝ) / 24 := by
        have : (u3_lb / 24 : ℕ) * 24 ≤ u3_lb := Nat.div_mul_le_self _ _
        have hcast : ((u3_lb / 24 : ℕ) : ℝ) * 24 ≤ u3_lb := by exact_mod_cast this
        linarith only [hcast]
      have hc6 : (u2_ub : ℝ) / 6 ≤ (((u2_ub + 5) / 6 : ℕ) : ℝ) := by
        have hlt : u2_ub ≤ ((u2_ub + 5) / 6) * 6 := by
          have := Nat.lt_div_mul_add (a := u2_ub + 5) (by norm_num : 0 < 6); omega
        have hcast : (u2_ub : ℝ) ≤ (((u2_ub + 5) / 6 : ℕ) : ℝ) * 6 := by exact_mod_cast hlt
        linarith only [hcast]
      have hc120 : (u4_ub : ℝ) / 120 ≤ (((u4_ub + 119) / 120 : ℕ) : ℝ) := by
        have hlt : u4_ub ≤ ((u4_ub + 119) / 120) * 120 := by
          have := Nat.lt_div_mul_add (a := u4_ub + 119) (by norm_num : 0 < 120); omega
        have hcast : (u4_ub : ℝ) ≤ (((u4_ub + 119) / 120 : ℕ) : ℝ) * 120 := by exact_mod_cast hlt
        linarith only [hcast]
      have hsub_le : (pos : ℝ) - (neg : ℝ) ≤ (p_alt : ℝ) := by
        dsimp [p_alt]
        by_cases hpn : neg ≤ pos
        · rw [Nat.cast_sub hpn]
        · have hpn' : pos ≤ neg := le_of_not_ge hpn
          rw [Nat.sub_eq_zero_of_le hpn', Nat.cast_zero]
          exact sub_nonpos.mpr (by exact_mod_cast hpn')
      have hpos_r : ((pos : ℝ) - neg) / S_nat =
          1 + (((u2_ub + 5) / 6 : ℕ) : ℝ) / S_nat + (((u4_ub + 119) / 120 : ℕ) : ℝ) / S_nat -
            ((u_lo / 2 : ℕ) : ℝ) / S_nat - ((u3_lb / 24 : ℕ) : ℝ) / S_nat := by
        dsimp [pos, neg]; push_cast; field_simp; ring
      have a2 : ((u_lo : ℝ) / S_nat) ^ 2 / 6 ≤ (((u2_ub + 5) / 6 : ℕ) : ℝ) / S_nat := by
        have h1 := div_le_div_of_nonneg_right hc6 hS.le
        have h2 := div_le_div_of_nonneg_right hu2_ub (by norm_num : (0 : ℝ) ≤ 6)
        have h3 : (u2_ub : ℝ) / 6 / S_nat = ((u2_ub : ℝ) / S_nat) / 6 := by ring
        linarith only [h1, h2, h3]
      have a4 : ((u_lo : ℝ) / S_nat) ^ 4 / 120 ≤ (((u4_ub + 119) / 120 : ℕ) : ℝ) / S_nat := by
        have h1 := div_le_div_of_nonneg_right hc120 hS.le
        have h2 := div_le_div_of_nonneg_right hu4_ub (by norm_num : (0 : ℝ) ≤ 120)
        have h3 : (u4_ub : ℝ) / 120 / S_nat = ((u4_ub : ℝ) / S_nat) / 120 := by ring
        linarith only [h1, h2, h3]
      have a1 : ((u_lo / 2 : ℕ) : ℝ) / S_nat ≤ ((u_lo : ℝ) / S_nat) / 2 := by
        have h1 := div_le_div_of_nonneg_right hd2 hS.le
        have h2 : (u_lo : ℝ) / 2 / S_nat = ((u_lo : ℝ) / S_nat) / 2 := by ring
        linarith only [h1, h2]
      have a3 : ((u3_lb / 24 : ℕ) : ℝ) / S_nat ≤ ((u_lo : ℝ) / S_nat) ^ 3 / 24 := by
        have h1 := div_le_div_of_nonneg_right hd24 hS.le
        have h2 := div_le_div_of_nonneg_right hu3_lb (by norm_num : (0 : ℝ) ≤ 24)
        have h3 : (u3_lb : ℝ) / 24 / S_nat = ((u3_lb : ℝ) / S_nat) / 24 := by ring
        linarith only [h1, h2, h3]
      have hdiv_pn := div_le_div_of_nonneg_right hsub_le hS.le
      linarith only [hpoly, hpos_r, a2, a4, a1, a3, hdiv_pn]
  -- Bound t * exp (-e_lo/S * t) ≤ um / S_nat
  have hum_bound : t * Real.exp (-((e_lo : ℝ) / S_nat) * t) ≤ (um : ℝ) / S_nat := by
    have he1_le : ((expLb8Nat S_nat : ℕ) : ℝ) / S_nat ≤ Real.exp 1 := by
      have := expLb8Nat_le_exp S_nat
      simpa [div_self hS.ne'] using this
    have he1_pos : 0 < ((expLb8Nat S_nat : ℕ) : ℝ) / S_nat := by
      have : 0 < expLb8Nat S_nat := lt_of_lt_of_le (by norm_num [S_nat]) (expLb8Nat_ge_S S_nat)
      positivity
    dsimp [um]
    split_ifs with hlo hhi
    · have h1_real : 1 ≤ ((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) := by
        have het0_le : (et0 : ℝ) / S_nat ≤ ((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) := fmul_le e_lo t0
        have hs_le : 1 ≤ (et0 : ℝ) / S_nat := by rw [one_le_div hS]; exact_mod_cast hlo
        linarith only [het0_le, hs_le]
      have huni := t_mul_exp_neg_le_unimax he_lo_r_pos (by positivity) ht0 ht1 he1_pos he1_le
      rw [if_pos h1_real] at huni
      have hexp_eb : ((expLb8Nat et0 : ℕ) : ℝ) / S_nat ≤ Real.exp (((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) :=
        le_trans (expLb8Nat_le_exp et0) (Real.exp_le_exp.mpr (by
          have := fmul_le e_lo t0; exact this))
      have hexp_pos : 0 < ((expLb8Nat et0 : ℕ) : ℝ) / S_nat := by
        have := expLb8Nat_ge_S et0
        have : 0 < expLb8Nat et0 := by dsimp [S_nat] at this; omega
        positivity
      have hinv : Real.exp (-((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) ≤
          1 / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat) := by
        have heq : -((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) = -(((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat)) := by ring
        rw [heq, Real.exp_neg, one_div]
        exact inv_anti₀ hexp_pos hexp_eb
      have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (t0 : ℝ) / S_nat)
      have hcd : (t0 : ℝ) / ((expLb8Nat et0 : ℕ) : ℝ) ≤ ((cdiv t0 (expLb8Nat et0) : ℕ) : ℝ) / S_nat :=
        le_cdiv t0 (expLb8Nat et0) (by have := expLb8Nat_ge_S et0; dsimp [S_nat] at this; omega)
      have heq_t : ((t0 : ℝ) / S_nat) * (1 / (((expLb8Nat et0 : ℕ) : ℝ) / S_nat)) =
          (t0 : ℝ) / ((expLb8Nat et0 : ℕ) : ℝ) := by field_simp
      linarith only [huni, hmul, heq_t, hcd]
    · have h1_real : ((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat) ≤ 1 := by
        have het1_le : ((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat) ≤ (et1 : ℝ) / S_nat := le_cmul e_lo t1
        have hs_le : (et1 : ℝ) / S_nat ≤ 1 := by rw [div_le_one hS]; exact_mod_cast hhi
        linarith only [het1_le, hs_le]
      have huni := t_mul_exp_neg_le_unimax he_lo_r_pos (by positivity) ht0 ht1 he1_pos he1_le
      have h_t1 : t * Real.exp (-((e_lo : ℝ) / S_nat) * t) ≤
          ((t1 : ℝ) / S_nat) * Real.exp (-((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat)) := by
        split_ifs at huni with h1a
        · have heq_t : ((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) = ((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat) := by
            have : ((e_lo : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) ≤ ((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat) :=
              mul_le_mul_of_nonneg_left (le_trans ht0 ht1) he_lo_r_pos.le
            linarith only [this, h1a, h1_real]
          have : (t0 : ℝ) / S_nat = (t1 : ℝ) / S_nat := mul_left_cancel₀ he_lo_r_pos.ne' heq_t
          rw [← this]; exact huni
        · exact huni
      have hexp_eb : ((expLb8Nat (fmul e_lo t1) : ℕ) : ℝ) / S_nat ≤
          Real.exp (((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat)) :=
        le_trans (expLb8Nat_le_exp (fmul e_lo t1)) (Real.exp_le_exp.mpr (fmul_le e_lo t1))
      have hexp_pos : 0 < ((expLb8Nat (fmul e_lo t1) : ℕ) : ℝ) / S_nat := by
        have := expLb8Nat_ge_S (fmul e_lo t1)
        have : 0 < expLb8Nat (fmul e_lo t1) := by dsimp [S_nat] at this; omega
        positivity
      have hinv : Real.exp (-((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat)) ≤
          1 / (((expLb8Nat (fmul e_lo t1) : ℕ) : ℝ) / S_nat) := by
        have heq : -((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat) = -(((e_lo : ℝ) / S_nat) * ((t1 : ℝ) / S_nat)) := by ring
        rw [heq, Real.exp_neg, one_div]
        exact inv_anti₀ hexp_pos hexp_eb
      have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (t1 : ℝ) / S_nat)
      have hcd : (t1 : ℝ) / ((expLb8Nat (fmul e_lo t1) : ℕ) : ℝ) ≤
          ((cdiv t1 (expLb8Nat (fmul e_lo t1)) : ℕ) : ℝ) / S_nat :=
        le_cdiv t1 (expLb8Nat (fmul e_lo t1))
          (by have := expLb8Nat_ge_S (fmul e_lo t1); dsimp [S_nat] at this; omega)
      have heq_t : ((t1 : ℝ) / S_nat) * (1 / (((expLb8Nat (fmul e_lo t1) : ℕ) : ℝ) / S_nat)) =
          (t1 : ℝ) / ((expLb8Nat (fmul e_lo t1) : ℕ) : ℝ) := by field_simp
      linarith only [h_t1, hmul, heq_t, hcd]
    · have hpk := t_mul_exp_neg_le_peak (t := t) he_lo_r_pos he1_pos he1_le
      have hden_le : ((fmul e_lo (expLb8Nat S_nat) : ℕ) : ℝ) / S_nat ≤
          ((e_lo : ℝ) / S_nat) * (((expLb8Nat S_nat : ℕ) : ℝ) / S_nat) := fmul_le e_lo (expLb8Nat S_nat)
      have hden_pos : 0 < fmul e_lo (expLb8Nat S_nat) := by
        have h1 : S_nat ≤ expLb8Nat S_nat := expLb8Nat_ge_S S_nat
        dsimp [fmul]
        rw [Nat.div_pos_iff]
        refine ⟨by norm_num [S_nat], ?_⟩
        exact le_trans (by dsimp [S_nat] at *; omega : S_nat ≤ 1 * S_nat)
          (Nat.mul_le_mul he_lo_pos h1)
      have h1 : 1 / (((e_lo : ℝ) / S_nat) * (((expLb8Nat S_nat : ℕ) : ℝ) / S_nat)) ≤
          (S_nat : ℝ) / ((fmul e_lo (expLb8Nat S_nat) : ℕ) : ℝ) := by
        have hpos_d : 0 < ((fmul e_lo (expLb8Nat S_nat) : ℕ) : ℝ) / S_nat := by positivity
        have hrw : (S_nat : ℝ) / ((fmul e_lo (expLb8Nat S_nat) : ℕ) : ℝ) =
            (((fmul e_lo (expLb8Nat S_nat) : ℕ) : ℝ) / S_nat)⁻¹ := by field_simp
        rw [one_div, hrw]
        exact inv_anti₀ hpos_d hden_le
      have hcd := le_cdiv S_nat (fmul e_lo (expLb8Nat S_nat)) hden_pos
      linarith only [hpk, h1, hcd]
  have hv2_bound : Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t) ≤
      (v2 : ℝ) / S_nat * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have hfac : Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t) =
        (2 * (y + 1 / 2 + m) * ((1 - Real.exp (-u_true)) / u_true) *
          (t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t))) * (2 * η * Real.exp (-y ^ 2 * t)) := by
      have hexp1 : Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) * Real.exp (-y ^ 2 * t) =
          Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexp2 : Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) * Real.exp (-u_true) =
          Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t) := by
        rw [← Real.exp_add]; congr 1; dsimp [u_true]; ring
      calc Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t)
          = Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) * (1 - Real.exp (-u_true)) := by
            rw [mul_sub, mul_one, hexp2]
        _ = (Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) * Real.exp (-y ^ 2 * t)) *
              (1 - Real.exp (-u_true)) := by rw [hexp1]
        _ = (2 * (y + 1 / 2 + m) * ((1 - Real.exp (-u_true)) / u_true) *
              (t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t))) * (2 * η * Real.exp (-y ^ 2 * t)) := by
            dsimp [u_true]; field_simp; ring
    have hpart1 : (1 - Real.exp (-u_true)) / u_true *
          (t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t)) ≤
        (cmul q_ub um : ℝ) / S_nat := by
      have ha : 0 ≤ (1 - Real.exp (-u_true)) / u_true := by
        have : Real.exp (-u_true) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hu_true_pos])
        exact div_nonneg (by linarith only [this]) hu_true_pos.le
      have hb : t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t) ≤ (um : ℝ) / S_nat :=
        le_trans (mul_le_mul_of_nonneg_left hexp_E_le ht.le) hum_bound
      have hc := mul_le_mul hq_bound hb (by positivity) (div_nonneg (Nat.cast_nonneg _) hS.le)
      exact le_trans hc (le_cmul q_ub um)
    have hpart2 : 2 * (y + 1 / 2 + m) *
          ((1 - Real.exp (-u_true)) / u_true * (t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t))) ≤
        (v2 : ℝ) / S_nat := by
      have h2w : 2 * (y + 1 / 2 + m) ≤ ((2 * w_hi : ℕ) : ℝ) / S_nat := by
        have hcast : ((2 * w_hi : ℕ) : ℝ) / S_nat = 2 * ((w_hi : ℝ) / S_nat) := by push_cast; ring
        rw [hcast]; linarith only [hw_hi_ge]
      have ha : 0 ≤ (1 - Real.exp (-u_true)) / u_true *
          (t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t)) := by
        have : Real.exp (-u_true) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hu_true_pos])
        exact mul_nonneg (div_nonneg (by linarith only [this]) hu_true_pos.le) (by positivity)
      have hm := mul_le_mul h2w hpart1 ha (div_nonneg (Nat.cast_nonneg _) hS.le)
      exact le_trans hm (le_cmul (2 * w_hi) (cmul q_ub um))
    rw [hfac]
    have hrew : 2 * (y + 1 / 2 + m) * ((1 - Real.exp (-u_true)) / u_true) *
          (t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t)) =
        2 * (y + 1 / 2 + m) * ((1 - Real.exp (-u_true)) / u_true *
          (t * Real.exp (-((y + 1 / 2 + m - η) ^ 2 - y ^ 2) * t))) := by ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_right hpart2 (by positivity)
  have hok_eq : okC2Step m y0 y1 t0 t1 e0 e1 =
      if e0 > 0 then min (cdiv (cdiv S_nat (2 * e0)) (expLb8Nat et0)) v2 else v2 := rfl
  rw [hok_eq]
  split_ifs with he0_pos
  · have hv1_bound := okC2Step_v1_sound he0_pos he_lo_r_pos ht0 he0 hη hexp_E_le
    rcases min_cases (cdiv (cdiv S_nat (2 * e0)) (expLb8Nat et0)) v2 with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]; exact hv1_bound
    · rw [hm]; exact hv2_bound
  · exact hv2_bound

private lemma okC2Nat_lhs_sound {y0 t0 e0 e1 : ℕ}
    (he01 : e0 < e1) (hy_lo : S_nat / 4 ≤ y0) (he_hi : e1 ≤ S_nat / 4)
    {y t η : ℝ} (hy0 : (y0 : ℝ) / S_nat ≤ y) (ht0 : (t0 : ℝ) / S_nat ≤ t)
    (he0 : (e0 : ℝ) / S_nat < η) (he1 : η ≤ (e1 : ℝ) / S_nat)
    (ht : 0 < t) :
    (let g1 := fmul (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
      let a1 := fmul g1 t0
      let ratio_lb := fdiv g1 e1
      let r2 := fmul ratio_lb ratio_lb
      let r3 := fmul r2 ratio_lb
      let t02 := fmul t0 t0
      let t03 := fmul t02 t0
      ((S_nat + fdiv a1 (2 * e1) + fmul (fmul r2 e0) t02 / 4 + fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ)) / S_nat *
        (2 * η * Real.exp (-y ^ 2 * t)) ≤
      Real.exp (-(y - 1 / 2 + η) ^ 2 * t) - 2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hy0_r_ge : (1 / 4 : ℝ) ≤ (y0 : ℝ) / S_nat := by
    have h1 : ((S_nat / 4 : ℕ) : ℝ) ≤ y0 := by exact_mod_cast hy_lo
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [h2, div_le_div_of_nonneg_right h1 hS.le]
  have he1_r_le : (e1 : ℝ) / S_nat ≤ 1 / 4 := by
    have h1 : (e1 : ℝ) ≤ ((S_nat / 4 : ℕ) : ℝ) := by exact_mod_cast he_hi
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [h2, div_le_div_of_nonneg_right h1 hS.le]
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) he0
  have hη14 : η ≤ 1 / 4 := le_trans he1 he1_r_le
  have hη12 : η < 1 / 2 := by linarith only [hη14]
  have hy_ge : 1 / 4 ≤ y := le_trans hy0_r_ge hy0
  set g1 := fmul (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
  set a1 := fmul g1 t0
  set ratio_lb := fdiv g1 e1
  set r2 := fmul ratio_lb ratio_lb
  set r3 := fmul r2 ratio_lb
  set t02 := fmul t0 t0
  set t03 := fmul t02 t0
  set lhs := S_nat + fdiv a1 (2 * e1) + fmul (fmul r2 e0) t02 / 4 + fmul (fmul r3 (fmul e0 e0)) t03 / 12
  change (lhs : ℝ) / S_nat * (2 * η * Real.exp (-y ^ 2 * t)) ≤ _
  have he1_pos : 0 < e1 := by omega
  have hhalf_e1 : e1 ≤ S_nat / 2 := by dsimp [S_nat] at *; omega
  have h2y_half : S_nat / 2 ≤ 2 * y0 := by dsimp [S_nat] at *; omega
  have hg1_le : (g1 : ℝ) / S_nat ≤ (1 / 2 - (e1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - 1 / 2 + (e1 : ℝ) / S_nat) := by
    have hfm := fmul_le (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
    have hhalf : ((S_nat / 2 : ℕ) : ℝ) / S_nat = 1 / 2 := by norm_num [S_nat]
    have ha : ((S_nat / 2 - e1 : ℕ) : ℝ) / S_nat = 1 / 2 - (e1 : ℝ) / S_nat := by
      rw [Nat.cast_sub hhalf_e1, sub_div, hhalf]
    have hb : ((2 * y0 - S_nat / 2 + e1 : ℕ) : ℝ) / S_nat = 2 * ((y0 : ℝ) / S_nat) - 1 / 2 + (e1 : ℝ) / S_nat := by
      rw [Nat.cast_add, Nat.cast_sub h2y_half]; push_cast; rw [← hhalf]; field_simp
    rw [← ha, ← hb]; exact hfm
  have hg1_nn : 0 ≤ (g1 : ℝ) / S_nat := by positivity
  have hratio_mono : (g1 : ℝ) / S_nat / ((e1 : ℝ) / S_nat) ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) / η := by
    have hd := div_le_div_of_nonneg_right hg1_le (by positivity : 0 ≤ (e1 : ℝ) / S_nat)
    have he₁_pos : 0 < (e1 : ℝ) / S_nat := by positivity
    have hsplit_e1 : (1 / 2 - (e1 : ℝ) / S_nat) * (2 * ((y0 : ℝ) / S_nat) - 1 / 2 + (e1 : ℝ) / S_nat) /
          ((e1 : ℝ) / S_nat) =
        (1 / (2 * ((e1 : ℝ) / S_nat)) - 1) * (2 * ((y0 : ℝ) / S_nat) - 1 / 2) + (1 / 2 - (e1 : ℝ) / S_nat) := by
      field_simp
    have hsplit_η : (1 / 2 - η) * (2 * y - 1 / 2 + η) / η =
        (1 / (2 * η) - 1) * (2 * y - 1 / 2) + (1 / 2 - η) := by
      field_simp
    have ha : 1 / (2 * ((e1 : ℝ) / S_nat)) - 1 ≤ 1 / (2 * η) - 1 := by
      have hinv : 1 / (2 * ((e1 : ℝ) / S_nat)) ≤ 1 / (2 * η) := by
        rw [one_div, one_div]; exact inv_anti₀ (by positivity) (by linarith only [he1])
      linarith only [hinv]
    have ha_nn : 0 ≤ 1 / (2 * ((e1 : ℝ) / S_nat)) - 1 := by
      have h2e : 2 * ((e1 : ℝ) / S_nat) ≤ 1 / 2 := by linarith only [he1_r_le]
      have hinv : 2 ≤ (2 * ((e1 : ℝ) / S_nat))⁻¹ := by
        rw [← one_div]; exact (le_div_iff₀ (by positivity)).mpr (by linarith only [h2e])
      rw [one_div]; linarith only [hinv]
    have hb : 2 * ((y0 : ℝ) / S_nat) - 1 / 2 ≤ 2 * y - 1 / 2 := by linarith only [hy0]
    have hb_nn : 0 ≤ 2 * ((y0 : ℝ) / S_nat) - 1 / 2 := by linarith only [hy0_r_ge]
    have hm := mul_le_mul ha hb hb_nn (by linarith only [ha, ha_nn])
    have hc : 1 / 2 - (e1 : ℝ) / S_nat ≤ 1 / 2 - η := by linarith only [he1]
    rw [hsplit_e1] at hd
    rw [hsplit_η]
    exact le_trans hd (add_le_add hm hc)
  have hr_lb_le : (ratio_lb : ℝ) / S_nat ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) / η := by
    have h1 := fdiv_le g1 e1 he1_pos
    have h2 : (g1 : ℝ) / e1 = ((g1 : ℝ) / S_nat) / ((e1 : ℝ) / S_nat) := by field_simp
    linarith only [hratio_mono, h1, h2]
  set A := (1 / 2 - η) * (2 * y - 1 / 2 + η) * t
  have hA_nn : 0 ≤ A := by
    have : 0 ≤ 1 / 2 - η := by linarith only [hη12]
    have : 0 ≤ 2 * y - 1 / 2 + η := by linarith only [hy_ge, hη0]
    positivity
  have hA_ge_a1 : ((fdiv a1 (2 * e1) : ℕ) : ℝ) / S_nat ≤ A / (2 * η) := by
    have h1 := fdiv_le a1 (2 * e1) (by omega)
    have h2 : (a1 : ℝ) / (2 * e1 : ℕ) = ((a1 : ℝ) / S_nat) / (2 * ((e1 : ℝ) / S_nat)) := by
      push_cast; field_simp
    have h3 : (a1 : ℝ) / S_nat ≤ ((g1 : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) := fmul_le g1 t0
    have heq : ((g1 : ℝ) / S_nat / ((e1 : ℝ) / S_nat)) * ((t0 : ℝ) / S_nat) / 2 =
        ((g1 : ℝ) / S_nat) * ((t0 : ℝ) / S_nat) / (2 * ((e1 : ℝ) / S_nat)) := by ring
    have heq2 : ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) * t / 2 = A / (2 * η) := by
      dsimp [A]; ring
    have h5 : ((g1 : ℝ) / S_nat / ((e1 : ℝ) / S_nat)) * ((t0 : ℝ) / S_nat) / 2 ≤
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) * t / 2 := by
      have ha := mul_le_mul hratio_mono ht0 (by positivity) (by
        have : 0 ≤ 1 / 2 - η := by linarith only [hη12]
        have : 0 ≤ 2 * y - 1 / 2 + η := by linarith only [hy_ge, hη0]
        positivity)
      linarith only [ha]
    have h7 := div_le_div_of_nonneg_right h3 (by positivity : 0 ≤ 2 * ((e1 : ℝ) / S_nat))
    linarith only [h1, h2, h7, heq, h5, heq2]
  have hA2_ge : ((fmul (fmul r2 e0) t02 / 4 : ℕ) : ℝ) / S_nat ≤ A ^ 2 / (4 * η) := by
    have hd4 : ((fmul (fmul r2 e0) t02 / 4 : ℕ) : ℝ) ≤ (fmul (fmul r2 e0) t02 : ℝ) / 4 := by
      have : (fmul (fmul r2 e0) t02 / 4 : ℕ) * 4 ≤ fmul (fmul r2 e0) t02 := Nat.div_mul_le_self _ _
      have : ((fmul (fmul r2 e0) t02 / 4 : ℕ) : ℝ) * 4 ≤ fmul (fmul r2 e0) t02 := by exact_mod_cast this
      linarith only [this]
    have h1 : ((fmul (fmul r2 e0) t02 / 4 : ℕ) : ℝ) / S_nat ≤
        ((fmul (fmul r2 e0) t02 : ℝ) / S_nat) / 4 := by
      have hdiv := div_le_div_of_nonneg_right hd4 hS.le
      have hrw : (fmul (fmul r2 e0) t02 : ℝ) / 4 / S_nat = ((fmul (fmul r2 e0) t02 : ℝ) / S_nat) / 4 := by ring
      linarith only [hdiv, hrw]
    have hr2 : (r2 : ℝ) / S_nat ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 2 := by
      have hfm := fmul_le ratio_lb ratio_lb
      have hsq := pow_le_pow_left₀ (by positivity) hr_lb_le 2
      linarith only [hfm, hsq, sq ((ratio_lb : ℝ) / S_nat)]
    have ht02 : (t02 : ℝ) / S_nat ≤ t ^ 2 := by
      have hfm := fmul_le t0 t0
      have hsq := pow_le_pow_left₀ (by positivity) ht0 2
      linarith only [hfm, hsq, sq ((t0 : ℝ) / S_nat)]
    have hprod : ((fmul (fmul r2 e0) t02 : ℝ) / S_nat) / 4 ≤
        (((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 2 * η * t ^ 2) / 4 := by
      have ha := fmul_le (fmul r2 e0) t02
      have hb := fmul_le r2 e0
      have hc : ((fmul r2 e0 : ℝ) / S_nat) ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 2 * η := by
        have hm := mul_le_mul hr2 he0.le (by positivity) (by positivity)
        linarith only [hb, hm]
      have hd := mul_le_mul hc ht02 (by positivity) (by positivity)
      linarith only [ha, hd]
    have heq : (((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 2 * η * t ^ 2) / 4 = A ^ 2 / (4 * η) := by
      dsimp [A]; field_simp
    linarith only [h1, hprod, heq]
  have hA3_ge : ((fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ) / S_nat ≤ A ^ 3 / (12 * η) := by
    have hd12 : ((fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ) ≤ (fmul (fmul r3 (fmul e0 e0)) t03 : ℝ) / 12 := by
      have : (fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) * 12 ≤ fmul (fmul r3 (fmul e0 e0)) t03 := Nat.div_mul_le_self _ _
      have : ((fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ) * 12 ≤ fmul (fmul r3 (fmul e0 e0)) t03 := by exact_mod_cast this
      linarith only [this]
    have h1 : ((fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ) / S_nat ≤
        ((fmul (fmul r3 (fmul e0 e0)) t03 : ℝ) / S_nat) / 12 := by
      have hdiv := div_le_div_of_nonneg_right hd12 hS.le
      have hrw : (fmul (fmul r3 (fmul e0 e0)) t03 : ℝ) / 12 / S_nat =
        ((fmul (fmul r3 (fmul e0 e0)) t03 : ℝ) / S_nat) / 12 := by ring
      linarith only [hdiv, hrw]
    have hr3 : (r3 : ℝ) / S_nat ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 3 := by
      have hfm := fmul_le r2 ratio_lb
      have hr2 : (r2 : ℝ) / S_nat ≤ ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 2 := by
        have hfa := fmul_le ratio_lb ratio_lb
        have hsq := pow_le_pow_left₀ (by positivity) hr_lb_le 2
        linarith only [hfa, hsq, sq ((ratio_lb : ℝ) / S_nat)]
      have hm := mul_le_mul hr2 hr_lb_le (by positivity) (by positivity)
      have hcb : ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 2 * ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) =
        ((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 3 := by ring
      linarith only [hfm, hm, hcb]
    have he02 : ((fmul e0 e0 : ℕ) : ℝ) / S_nat ≤ η ^ 2 := by
      have hfa := fmul_le e0 e0
      have hsq := pow_le_pow_left₀ (by positivity) he0.le 2
      linarith only [hfa, hsq, sq ((e0 : ℝ) / S_nat)]
    have ht03 : (t03 : ℝ) / S_nat ≤ t ^ 3 := by
      have hfm := fmul_le t02 t0
      have ht02 : (t02 : ℝ) / S_nat ≤ t ^ 2 := by
        have hfa := fmul_le t0 t0
        have hsq := pow_le_pow_left₀ (by positivity) ht0 2
        linarith only [hfa, hsq, sq ((t0 : ℝ) / S_nat)]
      have hm := mul_le_mul ht02 ht0 (by positivity) (by positivity)
      linarith only [hfm, hm, show t ^ 2 * t = t ^ 3 by ring]
    have hprod : ((fmul (fmul r3 (fmul e0 e0)) t03 : ℝ) / S_nat) / 12 ≤
        (((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 3 * η ^ 2 * t ^ 3) / 12 := by
      have ha := fmul_le (fmul r3 (fmul e0 e0)) t03
      have hb := fmul_le r3 (fmul e0 e0)
      have hr_nn : 0 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) / η := by
        have : 0 ≤ 1 / 2 - η := by linarith only [hη12]
        have : 0 ≤ 2 * y - 1 / 2 + η := by linarith only [hy_ge, hη0]
        positivity
      have hm1 := mul_le_mul hr3 he02 (by positivity) (pow_nonneg hr_nn 3)
      have hm2 := mul_le_mul (le_trans hb hm1) ht03 (by positivity) (mul_nonneg (pow_nonneg hr_nn 3) (sq_nonneg η))
      linarith only [ha, hm2]
    have heq : (((1 / 2 - η) * (2 * y - 1 / 2 + η) / η) ^ 3 * η ^ 2 * t ^ 3) / 12 = A ^ 3 / (12 * η) := by
      dsimp [A]; field_simp
    linarith only [h1, hprod, heq]
  clear_value g1 a1 ratio_lb r2 r3 t02 t03
  have hlhs_cast : (lhs : ℝ) / S_nat = 1 + ((fdiv a1 (2 * e1) : ℕ) : ℝ) / S_nat +
      ((fmul (fmul r2 e0) t02 / 4 : ℕ) : ℝ) / S_nat +
      ((fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ) / S_nat := by
    dsimp [lhs]; push_cast; field_simp
  have hexpA := exp_ge_poly3 hA_nn
  have hlhs_exp : (lhs : ℝ) / S_nat ≤ 1 + (Real.exp A - 1) / (2 * η) := by
    have hdiv : (A + A ^ 2 / 2 + A ^ 3 / 6) / (2 * η) ≤ (Real.exp A - 1) / (2 * η) :=
      div_le_div_of_nonneg_right (by linarith only [hexpA]) (by positivity)
    have hsum : (A + A ^ 2 / 2 + A ^ 3 / 6) / (2 * η) = A / (2 * η) + A ^ 2 / (4 * η) + A ^ 3 / (12 * η) := by
      ring
    linarith only [hlhs_cast, hA_ge_a1, hA2_ge, hA3_ge, hdiv, hsum]
  have heq_rhs : (1 + (Real.exp A - 1) / (2 * η)) * (2 * η * Real.exp (-y ^ 2 * t)) =
      Real.exp (-(y - 1 / 2 + η) ^ 2 * t) - 2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) := by
    have hexp_split : Real.exp A * Real.exp (-y ^ 2 * t) = Real.exp (-(y - 1 / 2 + η) ^ 2 * t) := by
      rw [← Real.exp_add]; congr 1; dsimp [A]; ring
    calc (1 + (Real.exp A - 1) / (2 * η)) * (2 * η * Real.exp (-y ^ 2 * t))
        = (2 * η + (Real.exp A - 1)) * Real.exp (-y ^ 2 * t) := by field_simp
      _ = Real.exp A * Real.exp (-y ^ 2 * t) - (1 - 2 * η) * Real.exp (-y ^ 2 * t) := by ring
      _ = Real.exp (-(y - 1 / 2 + η) ^ 2 * t) - 2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) := by
          rw [hexp_split]; ring
  have hmul_l := mul_le_mul_of_nonneg_right hlhs_exp (by positivity : 0 ≤ 2 * η * Real.exp (-y ^ 2 * t))
  exact le_trans hmul_l (le_of_eq heq_rhs)

private lemma okC2Nat_tail_sound {y0 t0 e0 e1 : ℕ}
    (hy_lo : S_nat / 4 ≤ y0) (ht_lo : 7 * S_nat / 10 ≤ t0) (he_hi : e1 ≤ S_nat / 4)
    {y t η : ℝ} (hy0 : (y0 : ℝ) / S_nat ≤ y) (ht0 : (t0 : ℝ) / S_nat ≤ t)
    (he0 : (e0 : ℝ) / S_nat < η) (he1 : η ≤ (e1 : ℝ) / S_nat)
    (ht : 0 < t) :
    ∑' m : ℕ, (Real.exp (-((y + 3) + 1 / 2 + m - η) ^ 2 * t) -
        Real.exp (-((y + 3) + 1 / 2 + m + η) ^ 2 * t)) ≤
      ((cdiv S_nat (expLb8Nat (fmul (fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)) t0)) : ℕ) : ℝ) /
        S_nat * (2 * η * Real.exp (-y ^ 2 * t)) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hy0_r_ge : (1 / 4 : ℝ) ≤ (y0 : ℝ) / S_nat := by
    have h1 : ((S_nat / 4 : ℕ) : ℝ) ≤ y0 := by exact_mod_cast hy_lo
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [h2, div_le_div_of_nonneg_right h1 hS.le]
  have he1_r_le : (e1 : ℝ) / S_nat ≤ 1 / 4 := by
    have h1 : (e1 : ℝ) ≤ ((S_nat / 4 : ℕ) : ℝ) := by exact_mod_cast he_hi
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [h2, div_le_div_of_nonneg_right h1 hS.le]
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) he0
  have hη14 : η ≤ 1 / 4 := le_trans he1 he1_r_le
  have hη12 : η < 1 / 2 := by linarith only [hη14]
  have hy_ge : 1 / 4 ≤ y := le_trans hy0_r_ge hy0
  set e_tail := fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)
  have haη : 0 ≤ (y + 3) - η := by linarith only [hy_ge, hη12]
  have hcond3 : 3 ≤ 2 * ((y + 3) - η) ^ 2 * t := by
    have ht710 : (7 / 10 : ℝ) ≤ t := by
      have h1 : ((7 * S_nat / 10 : ℕ) : ℝ) / S_nat ≤ (t0 : ℝ) / S_nat :=
        div_le_div_of_nonneg_right (by exact_mod_cast ht_lo) hS.le
      have h7 : ((7 * S_nat / 10 : ℕ) : ℝ) / S_nat = 7 / 10 := by norm_num [S_nat]
      linarith only [h1, h7, ht0]
    have hyn : 3 ≤ (y + 3) - η := by linarith only [hy_ge, hη14]
    nlinarith only [hyn, ht710]
  have hs3 : Summable (fun m : ℕ => Real.exp (-((y + 3) + 1 / 2 + m - η) ^ 2 * t) -
      Real.exp (-((y + 3) + 1 / 2 + m + η) ^ 2 * t)) :=
    (P5_gauss_bounds (y + 3) η t hη0 ht).1
  have hconv := gaussian_convex_tail_sum_le haη hη0 ht hcond3 hs3
  have hsub1 : e1 ≤ 3 * S_nat := by dsimp [S_nat] at *; omega
  have hsub2 : e1 ≤ 2 * y0 + 3 * S_nat := by dsimp [S_nat] at *; omega
  have het_le : (e_tail : ℝ) / S_nat ≤ (3 - η) * (2 * y + 3 - η) := by
    have hfm := fmul_le (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)
    have ha : ((3 * S_nat - e1 : ℕ) : ℝ) / S_nat = 3 - (e1 : ℝ) / S_nat := by
      rw [Nat.cast_sub hsub1]; push_cast; field_simp
    have hb : ((2 * y0 + 3 * S_nat - e1 : ℕ) : ℝ) / S_nat = 2 * ((y0 : ℝ) / S_nat) + 3 - (e1 : ℝ) / S_nat := by
      rw [Nat.cast_sub hsub2]; push_cast; field_simp
    have ha_le : ((3 * S_nat - e1 : ℕ) : ℝ) / S_nat ≤ 3 - η := by linarith only [ha, he1]
    have hb_le : ((2 * y0 + 3 * S_nat - e1 : ℕ) : ℝ) / S_nat ≤ 2 * y + 3 - η := by linarith only [hb, hy0, he1]
    exact le_trans hfm (mul_le_mul ha_le hb_le (by positivity) (by linarith only [hη12]))
  have hett_le : ((fmul e_tail t0 : ℕ) : ℝ) / S_nat ≤ (3 - η) * (2 * y + 3 - η) * t := by
    have h1 := fmul_le e_tail t0
    have hm := mul_le_mul het_le ht0 (div_nonneg (Nat.cast_nonneg t0) hS.le)
      (mul_nonneg (by linarith only [hη14]) (by linarith only [hy_ge, hη14]))
    linarith only [h1, hm]
  have hexp_eb : ((expLb8Nat (fmul e_tail t0) : ℕ) : ℝ) / S_nat ≤
      Real.exp ((3 - η) * (2 * y + 3 - η) * t) :=
    le_trans (expLb8Nat_le_exp (fmul e_tail t0)) (Real.exp_le_exp.mpr hett_le)
  have hexp_pos : 0 < ((expLb8Nat (fmul e_tail t0) : ℕ) : ℝ) / S_nat := by
    have hlt : 0 < expLb8Nat (fmul e_tail t0) :=
      lt_of_lt_of_le (by norm_num [S_nat] : 0 < S_nat) (expLb8Nat_ge_S (fmul e_tail t0))
    exact div_pos (Nat.cast_pos.mpr hlt) hS
  have hinv : Real.exp (-((y + 3 - η) ^ 2 - y ^ 2) * t) ≤
      ((cdiv S_nat (expLb8Nat (fmul e_tail t0)) : ℕ) : ℝ) / S_nat := by
    have hfac : (y + 3 - η) ^ 2 - y ^ 2 = (3 - η) * (2 * y + 3 - η) := by ring
    rw [hfac]
    have h1 : Real.exp (-((3 - η) * (2 * y + 3 - η) * t)) ≤
        1 / (((expLb8Nat (fmul e_tail t0) : ℕ) : ℝ) / S_nat) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ hexp_pos hexp_eb
    have h2 : 1 / (((expLb8Nat (fmul e_tail t0) : ℕ) : ℝ) / S_nat) =
        (S_nat : ℝ) / ((expLb8Nat (fmul e_tail t0) : ℕ) : ℝ) := by field_simp [hS.ne']
    have h3 := le_cdiv S_nat (expLb8Nat (fmul e_tail t0))
      (lt_of_lt_of_le (by norm_num [S_nat] : 0 < S_nat) (expLb8Nat_ge_S (fmul e_tail t0)))
    rw [show -((3 - η) * (2 * y + 3 - η)) * t = -((3 - η) * (2 * y + 3 - η) * t) by ring]
    linarith only [h1, h2, h3]
  have hexp_eq : 2 * η * Real.exp (-(y + 3 - η) ^ 2 * t) =
      Real.exp (-((y + 3 - η) ^ 2 - y ^ 2) * t) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have ha : Real.exp (-((y + 3 - η) ^ 2 - y ^ 2) * t) * Real.exp (-y ^ 2 * t) =
        Real.exp (-(y + 3 - η) ^ 2 * t) := by rw [← Real.exp_add]; congr 1; ring
    calc 2 * η * Real.exp (-(y + 3 - η) ^ 2 * t)
        = 2 * η * (Real.exp (-((y + 3 - η) ^ 2 - y ^ 2) * t) * Real.exp (-y ^ 2 * t)) := by rw [ha]
      _ = Real.exp (-((y + 3 - η) ^ 2 - y ^ 2) * t) * (2 * η * Real.exp (-y ^ 2 * t)) := by ring
  have hm := mul_le_mul_of_nonneg_right hinv (by positivity : 0 ≤ 2 * η * Real.exp (-y ^ 2 * t))
  have hexp_y3 : Real.exp (-((y + 3) - η) ^ 2 * t) = Real.exp (-(y + 3 - η) ^ 2 * t) := by
    congr 1
  linarith only [hconv, hm, hexp_eq, hexp_y3]

private lemma okC2Nat_sound {y0 y1 t0 t1 e0 e1 : ℕ}
    (hy01 : y0 ≤ y1) (ht01 : t0 ≤ t1) (he01 : e0 < e1)
    (hy_lo : S_nat / 4 ≤ y0) (ht_lo : 7 * S_nat / 10 ≤ t0) (he_hi : e1 ≤ S_nat / 4)
    (hok : okC2Nat y0 y1 t0 t1 e0 e1 = true)
    {y t η : ℝ} (hy0 : (y0 : ℝ) / S_nat ≤ y) (hy1 : y ≤ (y1 : ℝ) / S_nat)
    (ht0 : (t0 : ℝ) / S_nat ≤ t) (ht1 : t ≤ (t1 : ℝ) / S_nat)
    (he0 : (e0 : ℝ) / S_nat < η) (he1 : η ≤ (e1 : ℝ) / S_nat)
    (h2b_neg : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by
  have hS : (0 : ℝ) < S_nat := by norm_num [S_nat]
  have hy0_r_ge : (1 / 4 : ℝ) ≤ (y0 : ℝ) / S_nat := by
    have h1 : ((S_nat / 4 : ℕ) : ℝ) ≤ y0 := by exact_mod_cast hy_lo
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [h2, div_le_div_of_nonneg_right h1 hS.le]
  have he1_r_le : (e1 : ℝ) / S_nat ≤ 1 / 4 := by
    have h1 : (e1 : ℝ) ≤ ((S_nat / 4 : ℕ) : ℝ) := by exact_mod_cast he_hi
    have h2 : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [h2, div_le_div_of_nonneg_right h1 hS.le]
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) he0
  have hη12 : η < 1 / 2 := by linarith only [he1, he1_r_le]
  have ht : 0 < t := lt_of_lt_of_le (by
    have : 0 < t0 := by dsimp [S_nat] at ht_lo; omega
    positivity) ht0
  by_cases h2b : y0 ≥ e1 ∧ 2 * (y0 - e1) * (y0 - e1) * t0 ≥ 3 * S_nat * S_nat * S_nat
  · exfalso
    rcases h2b with ⟨hye, h2⟩
    have hdiff : ((y0 - e1 : ℕ) : ℝ) / S_nat ≤ y - η := by
      rw [Nat.cast_sub hye, sub_div]; linarith only [hy0, he1]
    have hsq : (((y0 - e1 : ℕ) : ℝ) / S_nat) ^ 2 ≤ (y - η) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdiff 2
    have hr : 3 * (S_nat : ℝ) ^ 3 ≤ 2 * ((y0 - e1 : ℕ) : ℝ) ^ 2 * t0 := by
      have : 3 * S_nat * S_nat * S_nat ≤ 2 * (y0 - e1) * (y0 - e1) * t0 := h2
      have : 3 * (S_nat : ℝ) * S_nat * S_nat ≤ 2 * ((y0 - e1 : ℕ) : ℝ) * ((y0 - e1 : ℕ) : ℝ) * t0 := by
        exact_mod_cast this
      linarith only [this, show (S_nat : ℝ) ^ 3 = S_nat * S_nat * S_nat by ring,
        show 2 * ((y0 - e1 : ℕ) : ℝ) ^ 2 * t0 = 2 * ((y0 - e1 : ℕ) : ℝ) * ((y0 - e1 : ℕ) : ℝ) * t0 by ring]
    have hprod : 3 ≤ 2 * (((y0 - e1 : ℕ) : ℝ) / S_nat) ^ 2 * ((t0 : ℝ) / S_nat) := by
      have heq : 2 * (((y0 - e1 : ℕ) : ℝ) / S_nat) ^ 2 * ((t0 : ℝ) / S_nat) =
          (2 * ((y0 - e1 : ℕ) : ℝ) ^ 2 * t0) / (S_nat : ℝ) ^ 3 := by ring
      rw [heq, le_div_iff₀ (by positivity)]
      exact hr
    have hyt : 2 * (((y0 - e1 : ℕ) : ℝ) / S_nat) ^ 2 * ((t0 : ℝ) / S_nat) ≤ 2 * (y - η) ^ 2 * t :=
      mul_le_mul (by linarith only [hsq]) ht0 (by positivity) (by positivity)
    linarith only [hprod, hyt, h2b_neg]
  · rcases case2_tsum_reindex y η t hη0 hη12 ht with ⟨_, hs2, hreidx⟩
    rw [hreidx]
    have hlhs_le := okC2Nat_lhs_sound he01 hy_lo he_hi hy0 ht0 he0 he1 ht
    have htail := okC2Nat_tail_sound hy_lo ht_lo he_hi hy0 ht0 he0 he1 ht
    have hok_le : okC2Step 0 y0 y1 t0 t1 e0 e1 + okC2Step 1 y0 y1 t0 t1 e0 e1 +
        okC2Step 2 y0 y1 t0 t1 e0 e1 +
        cdiv S_nat (expLb8Nat (fmul (fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)) t0)) ≤
        (let g1 := fmul (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
        let a1 := fmul g1 t0
        let ratio_lb := fdiv g1 e1
        let r2 := fmul ratio_lb ratio_lb
        let r3 := fmul r2 ratio_lb
        let t02 := fmul t0 t0
        let t03 := fmul t02 t0
        S_nat + fdiv a1 (2 * e1) + fmul (fmul r2 e0) t02 / 4 + fmul (fmul r3 (fmul e0 e0)) t03 / 12) := by
      have heq_ok : okC2Nat y0 y1 t0 t1 e0 e1 =
          decide ((let g1 := fmul (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
            let a1 := fmul g1 t0
            let ratio_lb := fdiv g1 e1
            let r2 := fmul ratio_lb ratio_lb
            let r3 := fmul r2 ratio_lb
            let t02 := fmul t0 t0
            let t03 := fmul t02 t0
            S_nat + fdiv a1 (2 * e1) + fmul (fmul r2 e0) t02 / 4 + fmul (fmul r3 (fmul e0 e0)) t03 / 12) ≥
            okC2Step 0 y0 y1 t0 t1 e0 e1 + okC2Step 1 y0 y1 t0 t1 e0 e1 +
              okC2Step 2 y0 y1 t0 t1 e0 e1 +
              cdiv S_nat (expLb8Nat (fmul (fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)) t0))) := by
        rw [okC2Nat, if_neg h2b]
      rw [heq_ok, decide_eq_true_eq] at hok
      exact hok
    have hm0 := okC2Step_sound (m := 0) hy01 ht01 he01.le hy_lo ht_lo he_hi hy0 hy1 ht0 ht1 he0 he1
    have hm1 := okC2Step_sound (m := 1) hy01 ht01 he01.le hy_lo ht_lo he_hi hy0 hy1 ht0 ht1 he0 he1
    have hm2 := okC2Step_sound (m := 2) hy01 ht01 he01.le hy_lo ht_lo he_hi hy0 hy1 ht0 ht1 he0 he1
    have hsplit3 := hs2.sum_add_tsum_nat_add 3
    have hsum3_eq : ∑ m ∈ Finset.range 3, (Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) -
          Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t)) =
        (Real.exp (-(y + 1 / 2 + (0 : ℕ) - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + (0 : ℕ) + η) ^ 2 * t)) +
        (Real.exp (-(y + 1 / 2 + (1 : ℕ) - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + (1 : ℕ) + η) ^ 2 * t)) +
        (Real.exp (-(y + 1 / 2 + (2 : ℕ) - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + (2 : ℕ) + η) ^ 2 * t)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.range_zero, Finset.sum_empty, zero_add]
    have htail_eq : ∑' m : ℕ, (Real.exp (-(y + 1 / 2 + ↑(m + 3) - η) ^ 2 * t) -
          Real.exp (-(y + 1 / 2 + ↑(m + 3) + η) ^ 2 * t)) =
        ∑' m : ℕ, (Real.exp (-((y + 3) + 1 / 2 + m - η) ^ 2 * t) -
          Real.exp (-((y + 3) + 1 / 2 + m + η) ^ 2 * t)) := by
      refine tsum_congr (fun m => ?_)
      have h1 : y + 1 / 2 + ↑(m + 3) - η = (y + 3) + 1 / 2 + m - η := by push_cast; ring
      have h2 : y + 1 / 2 + ↑(m + 3) + η = (y + 3) + 1 / 2 + m + η := by push_cast; ring
      rw [h1, h2]
    have hcmp_nat : ((okC2Step 0 y0 y1 t0 t1 e0 e1 + okC2Step 1 y0 y1 t0 t1 e0 e1 +
        okC2Step 2 y0 y1 t0 t1 e0 e1 +
        cdiv S_nat (expLb8Nat (fmul (fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)) t0)) : ℕ) : ℝ) / S_nat ≤
        (let g1 := fmul (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
          let a1 := fmul g1 t0
          let ratio_lb := fdiv g1 e1
          let r2 := fmul ratio_lb ratio_lb
          let r3 := fmul r2 ratio_lb
          let t02 := fmul t0 t0
          let t03 := fmul t02 t0
          ((S_nat + fdiv a1 (2 * e1) + fmul (fmul r2 e0) t02 / 4 + fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ)) / S_nat := by
      exact div_le_div_of_nonneg_right (by dsimp only; exact Nat.cast_le.mpr hok_le) hS.le
    have hmul_c := mul_le_mul_of_nonneg_right hcmp_nat (by positivity : 0 ≤ 2 * η * Real.exp (-y ^ 2 * t))
    have hrhs_split : ((okC2Step 0 y0 y1 t0 t1 e0 e1 + okC2Step 1 y0 y1 t0 t1 e0 e1 +
        okC2Step 2 y0 y1 t0 t1 e0 e1 +
        cdiv S_nat (expLb8Nat (fmul (fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)) t0)) : ℕ) : ℝ) / S_nat *
          (2 * η * Real.exp (-y ^ 2 * t)) =
        ((okC2Step 0 y0 y1 t0 t1 e0 e1 : ℕ) : ℝ) / S_nat * (2 * η * Real.exp (-y ^ 2 * t)) +
        ((okC2Step 1 y0 y1 t0 t1 e0 e1 : ℕ) : ℝ) / S_nat * (2 * η * Real.exp (-y ^ 2 * t)) +
        ((okC2Step 2 y0 y1 t0 t1 e0 e1 : ℕ) : ℝ) / S_nat * (2 * η * Real.exp (-y ^ 2 * t)) +
        ((cdiv S_nat (expLb8Nat (fmul (fmul (3 * S_nat - e1) (2 * y0 + 3 * S_nat - e1)) t0)) : ℕ) : ℝ) / S_nat *
          (2 * η * Real.exp (-y ^ 2 * t)) := by
      push_cast; ring
    have hsum_tail_le : ∑' m : ℕ, (Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) -
          Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t)) ≤
        (let g1 := fmul (S_nat / 2 - e1) (2 * y0 - S_nat / 2 + e1)
        let a1 := fmul g1 t0
        let ratio_lb := fdiv g1 e1
        let r2 := fmul ratio_lb ratio_lb
        let r3 := fmul r2 ratio_lb
        let t02 := fmul t0 t0
        let t03 := fmul t02 t0
        ((S_nat + fdiv a1 (2 * e1) + fmul (fmul r2 e0) t02 / 4 + fmul (fmul r3 (fmul e0 e0)) t03 / 12 : ℕ) : ℝ)) / S_nat *
          (2 * η * Real.exp (-y ^ 2 * t)) := by
      have htsum_eq : ∑' m : ℕ, (Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) -
            Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t)) =
          (Real.exp (-(y + 1 / 2 + (0 : ℕ) - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + (0 : ℕ) + η) ^ 2 * t)) +
          (Real.exp (-(y + 1 / 2 + (1 : ℕ) - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + (1 : ℕ) + η) ^ 2 * t)) +
          (Real.exp (-(y + 1 / 2 + (2 : ℕ) - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + (2 : ℕ) + η) ^ 2 * t)) +
          ∑' m : ℕ, (Real.exp (-((y + 3) + 1 / 2 + m - η) ^ 2 * t) -
            Real.exp (-((y + 3) + 1 / 2 + m + η) ^ 2 * t)) := by
        have hsp := hsplit3.symm
        dsimp only at hsp
        rw [hsp, hsum3_eq, htail_eq]
      rw [htsum_eq]
      exact le_trans (add_le_add (add_le_add (add_le_add hm0 hm1) hm2) htail)
        (le_trans (le_of_eq hrhs_split.symm) hmul_c)
    dsimp only at hlhs_le hsum_tail_le
    linarith only [hlhs_le, hsum_tail_le]

private lemma verifyTree_c2_sound :
    ∀ (tr : BoxTree) (y0 y1 t0 t1 e0 e1 : ℕ),
      S_nat / 4 ≤ y0 → 7 * S_nat / 10 ≤ t0 → e1 ≤ S_nat / 4 →
      verifyTree okC2Nat tr y0 y1 t0 t1 e0 e1 = true →
      ∀ {y t η : ℝ}, (y0 : ℝ) / S_nat ≤ y → y ≤ (y1 : ℝ) / S_nat →
        (t0 : ℝ) / S_nat ≤ t → t ≤ (t1 : ℝ) / S_nat →
        (e0 : ℝ) / S_nat < η → η ≤ (e1 : ℝ) / S_nat →
        2 * (y - η) ^ 2 * t < 3 →
        2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
          ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
            Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t))
  | .leaf, y0, y1, t0, t1, e0, e1, hy_lo, ht_lo, he_hi, hok, y, t, η, hy0, hy1, ht0, ht1, he0, he1, h2b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact okC2Nat_sound hok.1.1 hok.1.2.1 hok.1.2.2 hy_lo ht_lo he_hi hok.2 hy0 hy1 ht0 ht1 he0 he1 h2b
  | .splitY ym l r, y0, y1, t0, t1, e0, e1, hy_lo, ht_lo, he_hi, hok, y, t, η, hy0, hy1, ht0, ht1, he0, he1, h2b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases hym : y ≤ (ym : ℝ) / S_nat
    · exact verifyTree_c2_sound l y0 ym t0 t1 e0 e1 hy_lo ht_lo he_hi hok.1.2 hy0 hym ht0 ht1 he0 he1 h2b
    · exact verifyTree_c2_sound r ym y1 t0 t1 e0 e1 (le_trans hy_lo hok.1.1.1) ht_lo he_hi hok.2
        (le_of_not_ge hym) hy1 ht0 ht1 he0 he1 h2b
  | .splitT tm l r, y0, y1, t0, t1, e0, e1, hy_lo, ht_lo, he_hi, hok, y, t, η, hy0, hy1, ht0, ht1, he0, he1, h2b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases htm : t ≤ (tm : ℝ) / S_nat
    · exact verifyTree_c2_sound l y0 y1 t0 tm e0 e1 hy_lo ht_lo he_hi hok.1.2 hy0 hy1 ht0 htm he0 he1 h2b
    · exact verifyTree_c2_sound r y0 y1 tm t1 e0 e1 hy_lo (le_trans ht_lo hok.1.1.1) he_hi hok.2
        hy0 hy1 (le_of_not_ge htm) ht1 he0 he1 h2b
  | .splitX xm l r, y0, y1, t0, t1, e0, e1, hy_lo, ht_lo, he_hi, hok, y, t, η, hy0, hy1, ht0, ht1, he0, he1, h2b => by
    simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases hxm : η ≤ (xm : ℝ) / S_nat
    · exact verifyTree_c2_sound l y0 y1 t0 t1 e0 xm hy_lo ht_lo (le_trans hok.1.1.2 he_hi) hok.1.2
        hy0 hy1 ht0 ht1 he0 hxm h2b
    · exact verifyTree_c2_sound r y0 y1 t0 t1 xm e1 hy_lo ht_lo he_hi hok.2
        hy0 hy1 ht0 ht1 (lt_of_not_ge hxm) he1 h2b


lemma gaussian_sum_ge_c2_box_aux {y η t : ℝ}
    (hy : 1 / 4 ≤ y) (hy_hi : y ≤ 18 / 10)
    (hη0 : 0 < η) (hη_le : η ≤ 1 / 4)
    (ht_lo : 7 / 10 < t) (ht_hi : t ≤ 4)
    (h2b_neg : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by
  have hy_lo : ((S_nat / 4 : ℕ) : ℝ) / S_nat ≤ y := by
    have : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [this, hy]
  have hy_hi' : y ≤ ((18 * S_nat / 10 : ℕ) : ℝ) / S_nat := by
    have : ((18 * S_nat / 10 : ℕ) : ℝ) / S_nat = 18 / 10 := by norm_num [S_nat]
    linarith only [this, hy_hi]
  have ht_lo' : ((7 * S_nat / 10 : ℕ) : ℝ) / S_nat ≤ t := by
    have : ((7 * S_nat / 10 : ℕ) : ℝ) / S_nat = 7 / 10 := by norm_num [S_nat]
    linarith only [this, ht_lo]
  have ht_hi' : t ≤ ((4 * S_nat : ℕ) : ℝ) / S_nat := by
    have : ((4 * S_nat : ℕ) : ℝ) / S_nat = 4 := by norm_num [S_nat]
    linarith only [this, ht_hi]
  have hη_hi' : η ≤ ((S_nat / 4 : ℕ) : ℝ) / S_nat := by
    have : ((S_nat / 4 : ℕ) : ℝ) / S_nat = 1 / 4 := by norm_num [S_nat]
    linarith only [this, hη_le]
  exact verifyTree_c2_sound c2Tree (S_nat / 4) (18 * S_nat / 10) (7 * S_nat / 10) (4 * S_nat)
    0 (S_nat / 4) le_rfl le_rfl le_rfl c2_verified hy_lo hy_hi' ht_lo' ht_hi'
    (by simp [hη0]) hη_hi' h2b_neg

end SolGammaHelpers

theorem solution {y η t : ℝ}
    (hy : 1 / 4 ≤ y) (hy_hi : y ≤ 18 / 10)
    (hη0 : 0 < η) (hη_le : η ≤ 1 / 4)
    (ht_lo : 7 / 10 < t) (ht_hi : t ≤ 4)
    (h2b_neg : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) :=
  SolGammaHelpers.gaussian_sum_ge_c2_box_aux hy hy_hi hη0 hη_le ht_lo ht_hi h2b_neg
