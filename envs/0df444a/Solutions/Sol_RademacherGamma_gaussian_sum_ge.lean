-- Prove2me | solution 1 for RademacherGamma_gaussian_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:23:21.967699+00:00
-- url     : https://prove2.me/submissions/a0b8afc0-3c74-4f14-8f94-ef492adc863f

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_RademacherGamma_p3_gauss_bounds
import Theorems.Thm_RademacherGamma_p5_gauss_bounds
import Theorems.Thm_RademacherGamma_gaussian_sum_ge_le_quarter
import Theorems.Thm_RademacherGamma_gaussian_sum_ge_c2_box
import Theorems.Thm_RademacherGamma_gaussian_sum_ge_2b_p3

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


private lemma gaussian_sum_ge_2a_big_gt {y η t : ℝ} (hy : 1 / 4 ≤ y) (hη0 : 0 < η)
    (hη_le : η ≤ 1 / 4) (ht : 4 ≤ t) (h4_gt : 1 < 4 * (y + 1 / 2) * η * t) :
    1 ≤ (2 * η * (10 / 11 : ℝ) + (1 / 2 - η) * (2 * y - 1 / 2 + η) * t) *
      Real.exp ((1 / 2 - η) * (2 * y + 1 / 2 - η) * t) := by
  set A := (1 / 2 - η) * (2 * y - 1 / 2 + η) * t
  set em0 := (1 / 2 - η) * (2 * y + 1 / 2 - η) * t
  have hem0_nn : 0 ≤ em0 := by
    have : 0 ≤ 1 / 2 - η := by linarith only [hη_le]
    have : 0 ≤ 2 * y + 1 / 2 - η := by linarith only [hy, hη_le]
    dsimp [em0]; positivity
  have hexp_p5 : 1 + em0 + em0 ^ 2 / 2 + em0 ^ 3 / 6 + em0 ^ 4 / 24 + em0 ^ 5 / 120 ≤ Real.exp em0 :=
    exp_ge_poly5 hem0_nn
  have hexp_p3 : 1 + em0 + em0 ^ 2 / 2 + em0 ^ 3 / 6 ≤ Real.exp em0 := exp_ge_poly3 hem0_nn
  by_cases hη316 : 3 / 16 ≤ η
  · have hA_lb : (1 / 2 - η) * η * t ≤ A := by
      have h1 : η ≤ 2 * y - 1 / 2 + η := by linarith only [hy]
      have h12 : (1 / 2 - η) * η ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) := by
        have : 0 ≤ 1 / 2 - η := by linarith only [hη_le]
        nlinarith only [h1, this]
      dsimp [A]; nlinarith only [h12, ht]
    have hlhs_l : (33 / 64 : ℝ) ≤ 2 * η * (10 / 11) + A := by
      have h1 : 1 / 4 ≤ 1 / 2 - η := by linarith only [hη_le]
      have h12 : 3 / 16 ≤ (1 / 2 - η) * η * 4 := by nlinarith only [h1, hη316]
      have hnn : 0 ≤ (1 / 2 - η) * η := by nlinarith only [hη0, hη_le]
      have h3 : (1 / 2 - η) * η * 4 ≤ (1 / 2 - η) * η * t := by nlinarith only [ht, hnn]
      linarith only [hA_lb, hη316, h12, h3]
    have hem0_l : 3 / 4 ≤ em0 := by
      have h1 : 1 / 4 ≤ 1 / 2 - η := by linarith only [hη_le]
      have h2 : 3 / 4 ≤ 2 * y + 1 / 2 - η := by linarith only [hy, hη_le]
      have h12 : 3 / 16 ≤ (1 / 2 - η) * (2 * y + 1 / 2 - η) := by nlinarith only [h1, h2]
      dsimp [em0]; nlinarith only [h12, ht]
    have hp3_l : (2 : ℝ) ≤ Real.exp em0 :=
      le_trans (by norm_num) (le_trans (exp_ge_poly3 (by norm_num : (0 : ℝ) ≤ 3 / 4)) (Real.exp_le_exp.mpr hem0_l))
    exact le_trans (by norm_num) (mul_le_mul hlhs_l hp3_l (by norm_num) (by linarith only [hlhs_l]))
  · have hη_lt316 : η < 3 / 16 := lt_of_not_ge hη316
    by_cases hη18 : 1 / 8 ≤ η
    · have hA_lb : (1 / 2 - η) * η * t ≤ A := by
        have h1 : η ≤ 2 * y - 1 / 2 + η := by linarith only [hy]
        have h12 : (1 / 2 - η) * η ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) := by
          have : 0 ≤ 1 / 2 - η := by linarith only [hη_le]
          nlinarith only [h1, this]
        dsimp [A]; nlinarith only [h12, ht]
      have hlhs_l : (2 * (1 / 8) * (10 / 11) + 5 / 32 : ℝ) ≤ 2 * η * (10 / 11) + A := by
        have h1 : 5 / 16 ≤ 1 / 2 - η := by linarith only [hη_lt316]
        have h2 : 5 / 32 ≤ (1 / 2 - η) * η * 4 := by nlinarith only [h1, hη18]
        have hnn : 0 ≤ (1 / 2 - η) * η := by nlinarith only [hη0, hη_le]
        have h3 : (1 / 2 - η) * η * 4 ≤ (1 / 2 - η) * η * t := by nlinarith only [ht, hnn]
        linarith only [hA_lb, hη18, h2, h3]
      have hem0_l : 65 / 64 ≤ em0 := by
        have h1 : 5 / 16 ≤ 1 / 2 - η := by linarith only [hη_lt316]
        have h2 : 13 / 16 ≤ 2 * y + 1 / 2 - η := by linarith only [hy, hη_lt316]
        have h12 : 65 / 256 ≤ (1 / 2 - η) * (2 * y + 1 / 2 - η) := by nlinarith only [h1, h2]
        dsimp [em0]; nlinarith only [h12, ht]
      have hp3_l : (27 / 10 : ℝ) ≤ Real.exp em0 :=
        le_trans (by norm_num) (le_trans (exp_ge_poly3 (by norm_num : (0 : ℝ) ≤ 65 / 64)) (Real.exp_le_exp.mpr hem0_l))
      exact le_trans (by norm_num) (mul_le_mul hlhs_l hp3_l (by norm_num) (by linarith only [hlhs_l]))
    · have hη_lt18 : η < 1 / 8 := lt_of_not_ge hη18
      by_cases hy12 : 1 / 2 ≤ y
      · have hA_lb : 3 / 4 ≤ A := by
          have h1 : 3 / 8 ≤ 1 / 2 - η := by linarith only [hη_lt18]
          have h2 : 1 / 2 ≤ 2 * y - 1 / 2 + η := by linarith only [hy12, hη0]
          have h12 : 3 / 16 ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) := by nlinarith only [h1, h2]
          dsimp [A]; nlinarith only [h12, ht]
        have hem0_l : 2 ≤ em0 := by
          have h1 : 3 / 8 ≤ 1 / 2 - η := by linarith only [hη_lt18]
          have h2 : 11 / 8 ≤ 2 * y + 1 / 2 - η := by linarith only [hy12, hη_lt18]
          have h12 : 33 / 64 ≤ (1 / 2 - η) * (2 * y + 1 / 2 - η) := by nlinarith only [h1, h2]
          dsimp [em0]; nlinarith only [h12, ht]
        have hp3_l : (5 : ℝ) ≤ Real.exp em0 :=
          le_trans (by norm_num) (le_trans (exp_ge_poly3 (by norm_num : (0 : ℝ) ≤ 2)) (Real.exp_le_exp.mpr hem0_l))
        exact le_trans (by norm_num) (mul_le_mul (by linarith only [hA_lb, hη0] : (3 / 4 : ℝ) ≤ 2 * η * (10 / 11) + A)
          hp3_l (by norm_num) (by linarith only [hA_lb, hη0]))
      · have hy_lt12 : y < 1 / 2 := lt_of_not_ge hy12
        have hηt : 1 / 4 ≤ η * t := by
          have h1 : 4 * (y + 1 / 2) < 4 := by linarith only [hy_lt12]
          have hηt_nn : 0 ≤ η * t := by nlinarith only [hη0, ht]
          have h2 : 4 * (y + 1 / 2) * (η * t) ≤ 4 * (η * t) := by nlinarith only [h1, hηt_nn]
          linarith only [h4_gt, h2]
        have hA_lb : (1 / 2 - η) * (1 / 4) ≤ A := by
          have h1 : 0 ≤ 1 / 2 - η := by linarith only [hη_lt18]
          have h2 : η ≤ 2 * y - 1 / 2 + η := by linarith only [hy]
          have h12 : (1 / 2 - η) * η ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) := by nlinarith only [h1, h2]
          have h12t : (1 / 2 - η) * (η * t) ≤ A := by dsimp [A]; nlinarith only [h12, ht]
          have h14 : (1 / 2 - η) * (1 / 4) ≤ (1 / 2 - η) * (η * t) := by nlinarith only [h1, hηt]
          linarith only [h14, h12t]
        have hem0_l : (1 / 2 - η) * (1 - η) * t ≤ em0 := by
          have h1 : 0 ≤ 1 / 2 - η := by linarith only [hη_lt18]
          have h2 : 1 - η ≤ 2 * y + 1 / 2 - η := by linarith only [hy]
          have h12 : (1 / 2 - η) * (1 - η) ≤ (1 / 2 - η) * (2 * y + 1 / 2 - η) := by nlinarith only [h1, h2]
          dsimp [em0]; nlinarith only [h12, ht]
        by_cases ht9 : 9 ≤ t
        · have hlhs_l : 3 / 32 ≤ 2 * η * (10 / 11) + A := by
            have : 3 / 32 ≤ (1 / 2 - η) * (1 / 4) := by linarith only [hη_lt18]
            linarith only [this, hA_lb, hη0]
          have hem0_9 : 189 / 64 ≤ em0 := by
            have h1 : 3 / 8 ≤ 1 / 2 - η := by linarith only [hη_lt18]
            have h2 : 7 / 8 ≤ 1 - η := by linarith only [hη_lt18]
            have h12 : 21 / 64 ≤ (1 / 2 - η) * (1 - η) := by nlinarith only [h1, h2]
            have : 189 / 64 ≤ (1 / 2 - η) * (1 - η) * t := by nlinarith only [h12, ht9]
            linarith only [this, hem0_l]
          have hp3_l : (12 : ℝ) ≤ Real.exp em0 :=
            le_trans (by norm_num) (le_trans (exp_ge_poly3 (by norm_num : (0 : ℝ) ≤ 189 / 64)) (Real.exp_le_exp.mpr hem0_9))
          exact le_trans (by norm_num) (mul_le_mul hlhs_l hp3_l (by norm_num) (by linarith only [hlhs_l]))
        · have ht_lt9 : t < 9 := lt_of_not_ge ht9
          by_cases hη112 : 1 / 12 ≤ η
          · have hA_lb12 : 5 / 36 ≤ A := by
              have h1 : 0 ≤ 1 / 2 - η := by linarith only [hη_lt18]
              have h2 : η ≤ 2 * y - 1 / 2 + η := by linarith only [hy]
              have h12 : (1 / 2 - η) * η ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) := by nlinarith only [h1, h2]
              have h12t : (1 / 2 - η) * η * 4 ≤ A := by
                have hnn : 0 ≤ (1 / 2 - η) * η := by nlinarith only [h1, hη0]
                have hm : (1 / 2 - η) * η * 4 ≤ (1 / 2 - η) * η * t := by nlinarith only [ht, hnn]
                have hm2 : (1 / 2 - η) * η * t ≤ A := by dsimp [A]; nlinarith only [h12, ht]
                linarith only [hm, hm2]
              have hquad : 0 ≤ 4 * (η - 1 / 12) * (5 / 12 - η) := by nlinarith only [hη112, hη_lt18]
              linarith only [h12t, hquad]
            have hlhs_l : (2 * (1 / 12) * (10 / 11) + 5 / 36 : ℝ) ≤ 2 * η * (10 / 11) + A := by
              linarith only [hA_lb12, hη112]
            have hem0_1 : 21 / 16 ≤ em0 := by
              have h1 : 3 / 8 ≤ 1 / 2 - η := by linarith only [hη_lt18]
              have h2 : 7 / 8 ≤ 1 - η := by linarith only [hη_lt18]
              have h12 : 21 / 64 ≤ (1 / 2 - η) * (1 - η) := by nlinarith only [h1, h2]
              have : 21 / 16 ≤ (1 / 2 - η) * (1 - η) * t := by nlinarith only [h12, ht]
              linarith only [this, hem0_l]
            have hp3_l : (7 / 2 : ℝ) ≤ Real.exp em0 :=
              le_trans (by norm_num) (le_trans (exp_ge_poly3 (by norm_num : (0 : ℝ) ≤ 21 / 16)) (Real.exp_le_exp.mpr hem0_1))
            exact le_trans (by norm_num) (mul_le_mul hlhs_l hp3_l (by norm_num) (by linarith only [hlhs_l]))
          · have hη_lt112 : η < 1 / 12 := lt_of_not_ge hη112
            by_cases ht92 : 9 / 2 ≤ t
            · have hlhs_l : 20 / 11 * η + 5 / 48 ≤ 2 * η * (10 / 11) + A := by
                have : 5 / 48 ≤ (1 / 2 - η) * (1 / 4) := by linarith only [hη_lt112]
                linarith only [this, hA_lb]
              have hηt_l : 5 / 11 / t + 5 / 48 ≤ 2 * η * (10 / 11) + A := by
                have ht0 : 0 < t := by linarith only [ht]
                have h2 : 5 / 11 / t ≤ 20 / 11 * η := by
                  rw [div_le_iff₀ ht0]; nlinarith only [hηt]
                linarith only [h2, hlhs_l]
              have hem0_t : 55 / 144 * t ≤ em0 := by
                have h1 : 5 / 12 ≤ 1 / 2 - η := by linarith only [hη_lt112]
                have h2 : 11 / 12 ≤ 1 - η := by linarith only [hη_lt112]
                have h12 : 55 / 144 ≤ (1 / 2 - η) * (1 - η) := by nlinarith only [h1, h2]
                nlinarith only [h12, ht, hem0_l]
              have hp3_t : 1 ≤ (5 / 11 / t + 5 / 48) * (1 + (55 / 144 * t) + (55 / 144 * t) ^ 2 / 2 + (55 / 144 * t) ^ 3 / 6) := by
                have ht0 : 0 < t := by linarith only [ht]
                rw [show (5 / 11 / t + 5 / 48) * (1 + (55 / 144 * t) + (55 / 144 * t) ^ 2 / 2 + (55 / 144 * t) ^ 3 / 6) =
                  (5 / 11 + 5 / 48 * t) * (1 + (55 / 144 * t) + (55 / 144 * t) ^ 2 / 2 + (55 / 144 * t) ^ 3 / 6) / t by
                    field_simp [ht0.ne']]
                rw [one_le_div ht0]
                have hs : 0 ≤ t - 9 / 2 := by linarith only [ht92]
                have hid : (5 / 11 + 5 / 48 * t) * (1 + (55 / 144 * t) + (55 / 144 * t) ^ 2 / 2 +
                      (55 / 144 * t) ^ 3 / 6) - t =
                    10746403 / 69206016 + 2370739 / 2359296 * (t - 9 / 2) + 275275 / 786432 * (t - 9 / 2) ^ 2 +
                      4189625 / 143327232 * (t - 9 / 2) ^ 3 + 831875 / 859963392 * (t - 9 / 2) ^ 4 := by ring
                have hpos : 0 ≤ 10746403 / 69206016 + 2370739 / 2359296 * (t - 9 / 2) +
                    275275 / 786432 * (t - 9 / 2) ^ 2 + 4189625 / 143327232 * (t - 9 / 2) ^ 3 +
                    831875 / 859963392 * (t - 9 / 2) ^ 4 := by positivity
                linarith only [hid, hpos]
              have hexp_ge_t : 1 + 55 / 144 * t + (55 / 144 * t) ^ 2 / 2 + (55 / 144 * t) ^ 3 / 6 ≤ Real.exp em0 := by
                have hnn : 0 ≤ 55 / 144 * t := by positivity
                have hsq : (55 / 144 * t) ^ 2 ≤ em0 ^ 2 := by nlinarith only [hem0_t, hnn]
                have hcb : (55 / 144 * t) ^ 3 ≤ em0 ^ 3 := by nlinarith only [hem0_t, hnn, hsq]
                have h1 : 1 + 55 / 144 * t + (55 / 144 * t) ^ 2 / 2 + (55 / 144 * t) ^ 3 / 6 ≤
                    1 + em0 + em0 ^ 2 / 2 + em0 ^ 3 / 6 := by linarith only [hem0_t, hsq, hcb]
                exact le_trans h1 hexp_p3
              exact le_trans hp3_t (mul_le_mul hηt_l hexp_ge_t (by positivity) (by linarith only [hη0, hA_lb]))
            · have ht_lt92 : t < 9 / 2 := lt_of_not_ge ht92
              have hη_ge118 : 1 / 18 ≤ η := by nlinarith only [hηt, ht_lt92, hη0]
              have hlhs_l : 1 / 8 + 69 / 44 * η ≤ 2 * η * (10 / 11) + A := by
                have h1 : 1 / 8 + 69 / 44 * η = 2 * η * (10 / 11) + (1 / 2 - η) * (1 / 4) := by ring
                linarith only [h1, hA_lb]
              by_cases hη115 : η ≤ 1 / 15
              · have hleft : (2121 / 10000 : ℝ) ≤ 2 * η * (10 / 11) + A := by linarith only [hlhs_l, hη_ge118]
                have hem0_16 : 1617 / 1000 ≤ em0 := by
                  have h1 : 1 / 2 - 1 / 15 ≤ 1 / 2 - η := by linarith only [hη115]
                  have h2 : 1 - 1 / 15 ≤ 1 - η := by linarith only [hη115]
                  have h12 : (1 / 2 - 1 / 15 : ℝ) * (1 - 1 / 15) ≤ (1 / 2 - η) * (1 - η) := by nlinarith only [h1, h2]
                  have h3 : 1617 / 1000 ≤ (1 / 2 - η) * (1 - η) * t := by nlinarith only [h12, ht]
                  linarith only [h3, hem0_l]
                have hp5_l : (49 / 10 : ℝ) ≤ Real.exp em0 :=
                  le_trans (by norm_num) (le_trans (exp_ge_poly5 (by norm_num : (0 : ℝ) ≤ 1617 / 1000)) (Real.exp_le_exp.mpr hem0_16))
                exact le_trans (by norm_num) (mul_le_mul hleft hp5_l (by norm_num) (by linarith only [hleft]))
              · have hη_gt115 : 1 / 15 < η := lt_of_not_ge hη115
                have hleft : (2295 / 10000 : ℝ) ≤ 2 * η * (10 / 11) + A := by linarith only [hlhs_l, hη_gt115]
                have hem0_15 : 1527 / 1000 ≤ em0 := by
                  have h1 : 1 / 2 - 1 / 12 ≤ 1 / 2 - η := by linarith only [hη_lt112]
                  have h2 : 1 - 1 / 12 ≤ 1 - η := by linarith only [hη_lt112]
                  have h12 : (1 / 2 - 1 / 12 : ℝ) * (1 - 1 / 12) ≤ (1 / 2 - η) * (1 - η) := by nlinarith only [h1, h2]
                  have h3 : 1527 / 1000 ≤ (1 / 2 - η) * (1 - η) * t := by nlinarith only [h12, ht]
                  linarith only [h3, hem0_l]
                have hp5_l : (458 / 100 : ℝ) ≤ Real.exp em0 :=
                  le_trans (by norm_num) (le_trans (exp_ge_poly5 (by norm_num : (0 : ℝ) ≤ 1527 / 1000)) (Real.exp_le_exp.mpr hem0_15))
                exact le_trans (by norm_num) (mul_le_mul hleft hp5_l (by norm_num) (by linarith only [hleft]))

private lemma gaussian_sum_ge_2a_big {y η t : ℝ} (hy : 1 / 4 ≤ y) (hη0 : 0 < η)
    (hη_le : η ≤ 1 / 4) (ht : 4 ≤ t) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hη12 : η < 1 / 2 := by linarith only [hη_le]
  rcases case2_tsum_reindex y η t hη0 hη12 ht0 with ⟨_, hs2, hreidx⟩
  rw [hreidx]
  have hsplit := hs2.sum_add_tsum_nat_add 1
  have hsum1 : ∑ m ∈ Finset.range 1, (Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) -
      Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t)) =
      Real.exp (-(y + 1 / 2 - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + η) ^ 2 * t) := by
    simp
  have htail_eq : ∑' m : ℕ, (Real.exp (-(y + 1 / 2 + ↑(m + 1) - η) ^ 2 * t) -
      Real.exp (-(y + 1 / 2 + ↑(m + 1) + η) ^ 2 * t)) =
      ∑' m : ℕ, (Real.exp (-((y + 1) + 1 / 2 + m - η) ^ 2 * t) -
        Real.exp (-((y + 1) + 1 / 2 + m + η) ^ 2 * t)) := by
    refine tsum_congr (fun m => ?_)
    have h1 : y + 1 / 2 + ↑(m + 1) - η = (y + 1) + 1 / 2 + m - η := by push_cast; ring
    have h2 : y + 1 / 2 + ↑(m + 1) + η = (y + 1) + 1 / 2 + m + η := by push_cast; ring
    rw [h1, h2]
  have htail : ∑' m : ℕ, (Real.exp (-((y + 1) + 1 / 2 + m - η) ^ 2 * t) -
      Real.exp (-((y + 1) + 1 / 2 + m + η) ^ 2 * t)) ≤
      (1 / 11 : ℝ) * (2 * η * Real.exp (-y ^ 2 * t)) := by
    have haη : 0 ≤ (y + 1) - η := by linarith only [hy, hη_le]
    have hcond3 : 3 ≤ 2 * ((y + 1) - η) ^ 2 * t := by
      have h1 : 1 ≤ ((y + 1) - η) ^ 2 := one_le_pow₀ (by linarith only [hy, hη_le])
      have h2 := mul_le_mul h1 ht (by norm_num) (by positivity)
      linarith only [h2]
    have hs3 := (P5_gauss_bounds (y + 1) η t hη0 ht0).1
    have hconv := gaussian_convex_tail_sum_le haη hη0 ht0 hcond3 hs3
    have hem1 : 15 / 4 ≤ ((y + 1 - η) ^ 2 - y ^ 2) * t := by
      have hfac : (y + 1 - η) ^ 2 - y ^ 2 = (1 - η) * (2 * y + 1 - η) := by ring
      rw [hfac]
      have h1 : 3 / 4 ≤ 1 - η := by linarith only [hη_le]
      have h2 : 5 / 4 ≤ 2 * y + 1 - η := by linarith only [hy, hη_le]
      have h12 : 15 / 16 ≤ (1 - η) * (2 * y + 1 - η) :=
        le_trans (by norm_num) (mul_le_mul h1 h2 (by norm_num) (by linarith only [h1]))
      have h12t := mul_le_mul h12 ht (by norm_num) (by linarith only [h12])
      linarith only [h12t]
    have hexp_eb : (11 : ℝ) ≤ Real.exp (((y + 1 - η) ^ 2 - y ^ 2) * t) := by
      have hp := exp_ge_poly2 (by linarith only [hem1] : 0 ≤ ((y + 1 - η) ^ 2 - y ^ 2) * t)
      have hsq : (15 / 4 : ℝ) ^ 2 ≤ (((y + 1 - η) ^ 2 - y ^ 2) * t) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hem1 2
      linarith only [hp, hem1, hsq]
    have hinv : Real.exp (-((y + 1 - η) ^ 2 - y ^ 2) * t) ≤ 1 / 11 := by
      have heq : -((y + 1 - η) ^ 2 - y ^ 2) * t = -(((y + 1 - η) ^ 2 - y ^ 2) * t) := by ring
      rw [heq, Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) hexp_eb
    have heq_e : 2 * η * Real.exp (-((y + 1) - η) ^ 2 * t) =
        Real.exp (-((y + 1 - η) ^ 2 - y ^ 2) * t) * (2 * η * Real.exp (-y ^ 2 * t)) := by
      have ha : Real.exp (-((y + 1 - η) ^ 2 - y ^ 2) * t) * Real.exp (-y ^ 2 * t) =
          Real.exp (-((y + 1) - η) ^ 2 * t) := by rw [← Real.exp_add]; congr 1; ring
      rw [← ha]; ring
    have hm := mul_le_mul_of_nonneg_right hinv (by positivity : 0 ≤ 2 * η * Real.exp (-y ^ 2 * t))
    linarith only [hconv, heq_e, hm]
  set A := (1 / 2 - η) * (2 * y - 1 / 2 + η) * t
  have hA_nn : 0 ≤ A := by
    have : 0 ≤ 1 / 2 - η := by linarith only [hη_le]
    have : 0 ≤ 2 * y - 1 / 2 + η := by linarith only [hy, hη0]
    dsimp [A]; positivity
  set em0 := (1 / 2 - η) * (2 * y + 1 / 2 - η) * t
  have hem0_nn : 0 ≤ em0 := by
    have : 0 ≤ 1 / 2 - η := by linarith only [hη_le]
    have : 0 ≤ 2 * y + 1 / 2 - η := by linarith only [hy, hη_le]
    dsimp [em0]; positivity
  have hm0_fac : Real.exp (-(y + 1 / 2 - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + η) ^ 2 * t) =
      Real.exp (-em0) * (1 - Real.exp (-4 * (y + 1 / 2) * η * t)) * Real.exp (-y ^ 2 * t) := by
    have h1 : -em0 + -y ^ 2 * t = -(y + 1 / 2 - η) ^ 2 * t := by dsimp [em0]; ring
    have h2 : -em0 + -4 * (y + 1 / 2) * η * t + -y ^ 2 * t = -(y + 1 / 2 + η) ^ 2 * t := by
      dsimp [em0]; ring
    rw [mul_sub, mul_one, sub_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, h1]
    congr 2; rw [h2]
  have hlhs_ge : (2 * η + A + A ^ 2 / 2 + A ^ 3 / 6) * Real.exp (-y ^ 2 * t) ≤
      Real.exp (-(y - 1 / 2 + η) ^ 2 * t) - 2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) := by
    have hexp := exp_ge_poly3 hA_nn
    have heq_e : Real.exp A * Real.exp (-y ^ 2 * t) = Real.exp (-(y - 1 / 2 + η) ^ 2 * t) := by
      rw [← Real.exp_add]; congr 1; dsimp [A]; ring
    have hm := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-y ^ 2 * t)).le
    linarith only [hm, heq_e,
      show (1 + A + A ^ 2 / 2 + A ^ 3 / 6) * Real.exp (-y ^ 2 * t) - 2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) =
        (2 * η + A + A ^ 2 / 2 + A ^ 3 / 6) * Real.exp (-y ^ 2 * t) by ring]
  have hcore : Real.exp (-em0) * (1 - Real.exp (-4 * (y + 1 / 2) * η * t)) ≤
      2 * η * (10 / 11 : ℝ) + A + A ^ 2 / 2 + A ^ 3 / 6 := by
    have hexp_p5 : 1 + em0 + em0 ^ 2 / 2 + em0 ^ 3 / 6 + em0 ^ 4 / 24 + em0 ^ 5 / 120 ≤ Real.exp em0 :=
      exp_ge_poly5 hem0_nn
    have hexp_p3 : 1 + em0 + em0 ^ 2 / 2 + em0 ^ 3 / 6 ≤ Real.exp em0 := exp_ge_poly3 hem0_nn
    by_cases h4 : 4 * (y + 1 / 2) * η * t ≤ 1
    · have hη_ub : η ≤ 1 / 12 := by
        have h1a : 3 ≤ 4 * (y + 1 / 2) := by linarith only [hy]
        have h1b : 3 * η ≤ 4 * (y + 1 / 2) * η := mul_le_mul_of_nonneg_right h1a hη0.le
        have h1 : 3 * η * 4 ≤ 4 * (y + 1 / 2) * η * t := mul_le_mul h1b ht (by norm_num) (by positivity)
        linarith only [h1, h4]
      have h1e : 1 - Real.exp (-4 * (y + 1 / 2) * η * t) ≤ 4 * (y + 1 / 2) * η * t := by
        have hex := exp_neg_ge_poly1 (x := 4 * (y + 1 / 2) * η * t)
        rw [show -(4 * (y + 1 / 2) * η * t) = -4 * (y + 1 / 2) * η * t by ring] at hex
        linarith only [hex]
      have hmul1 : Real.exp (-em0) * (1 - Real.exp (-4 * (y + 1 / 2) * η * t)) ≤
          Real.exp (-em0) * (4 * (y + 1 / 2) * η * t) :=
        mul_le_mul_of_nonneg_left h1e (Real.exp_pos _).le
      have hA_lb : 5 / 12 * η * t ≤ A := by
        have h1 : 5 / 12 ≤ 1 / 2 - η := by linarith only [hη_ub]
        have h2 : η ≤ 2 * y - 1 / 2 + η := by linarith only [hy]
        have h12 : 5 / 12 * η ≤ (1 / 2 - η) * (2 * y - 1 / 2 + η) := mul_le_mul h1 h2 hη0.le (by linarith only [h1])
        dsimp [A]; exact mul_le_mul_of_nonneg_right h12 ht0.le
      have hem0_lb : (y + 1 / 2) * t / 2 ≤ em0 := by
        have h1 : 5 / 12 ≤ 1 / 2 - η := by linarith only [hη_ub]
        have h2 : 11 * (2 * y + 1) ≤ 18 * (2 * y + 1 / 2 - η) := by linarith only [hy, hη_ub]
        have h12 : 55 / 108 * (y + 1 / 2) ≤ (1 / 2 - η) * (2 * y + 1 / 2 - η) := by
          have hy_nn : 0 ≤ 2 * y + 1 := by linarith only [hy]
          have hm := mul_le_mul h1 h2 (by positivity) (by linarith only [h1])
          linarith only [hm]
        have h3 : 55 / 108 * ((y + 1 / 2) * t) ≤ em0 := by
          dsimp [em0]
          rw [show 55 / 108 * ((y + 1 / 2) * t) = (55 / 108 * (y + 1 / 2)) * t by ring]
          exact mul_le_mul_of_nonneg_right h12 ht0.le
        have hyt_nn : 0 ≤ (y + 1 / 2) * t := mul_nonneg (by linarith only [hy]) ht0.le
        linarith only [h3, hyt_nn]
      set u := 2 * (y + 1 / 2) * t
      have hu6 : 6 ≤ u := by
        have h1 : 3 / 2 ≤ 2 * (y + 1 / 2) := by linarith only [hy]
        dsimp [u]
        have hm := mul_le_mul h1 ht (by norm_num) (by positivity)
        linarith only [hm]
      have hem0_u : u / 4 ≤ em0 := by dsimp [u]; linarith only [hem0_lb]
      have hpoly_u : 2 * u ≤ (20 / 11 + 5 / 12 * t) * (1 + em0 + em0 ^ 2 / 2 + em0 ^ 3 / 6) := by
        have h5t : 41 / 12 ≤ 20 / 11 + 5 / 12 * t := by linarith only [ht]
        have hu_nn : 0 ≤ u / 4 := by linarith only [hu6]
        have hsq : (u / 4) ^ 2 ≤ em0 ^ 2 := pow_le_pow_left₀ hu_nn hem0_u 2
        have hcb : (u / 4) ^ 3 ≤ em0 ^ 3 := pow_le_pow_left₀ hu_nn hem0_u 3
        have hp3 : 1 + u / 4 + (u / 4) ^ 2 / 2 + (u / 4) ^ 3 / 6 ≤ 1 + em0 + em0 ^ 2 / 2 + em0 ^ 3 / 6 := by
          linarith only [hem0_u, hsq, hcb]
        have h1d : 2 * u ≤ 41 / 12 * (1 + u / 4 + (u / 4) ^ 2 / 2 + (u / 4) ^ 3 / 6) := by
          have hw : 0 ≤ u - 6 := by linarith only [hu6]
          have hid : 41 / 12 * (1 + u / 4 + (u / 4) ^ 2 / 2 + (u / 4) ^ 3 / 6) - 2 * u =
              443 / 192 + 421 / 384 * (u - 6) + 205 / 768 * (u - 6) ^ 2 + 41 / 4608 * (u - 6) ^ 3 := by ring
          have hpos : 0 ≤ 443 / 192 + 421 / 384 * (u - 6) + 205 / 768 * (u - 6) ^ 2 +
              41 / 4608 * (u - 6) ^ 3 := by positivity
          linarith only [hid, hpos]
        have hp3_nn : 0 ≤ 1 + u / 4 + (u / 4) ^ 2 / 2 + (u / 4) ^ 3 / 6 := by positivity
        exact le_trans h1d (mul_le_mul h5t hp3 hp3_nn (by linarith only [h5t]))
      have hinv : Real.exp (-em0) * (2 * u) ≤ 20 / 11 + 5 / 12 * t := by
        rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos em0)]
        have hp_pos : 0 ≤ 20 / 11 + 5 / 12 * t := by linarith only [ht]
        exact le_trans hpoly_u (mul_le_mul_of_nonneg_left hexp_p3 hp_pos)
      have hfin_A : (20 / 11 + 5 / 12 * t) * η ≤ 2 * η * (10 / 11) + A := by
        have h1 : 5 / 12 * t * η = 5 / 12 * η * t := by ring
        linarith only [hA_lb, h1]
      have hm_eta := mul_le_mul_of_nonneg_right hinv hη0.le
      have heq_u : Real.exp (-em0) * (4 * (y + 1 / 2) * η * t) = Real.exp (-em0) * (2 * u) * η := by
        dsimp [u]; ring
      have hA_rest : 0 ≤ A ^ 2 / 2 + A ^ 3 / 6 := by positivity
      linarith only [hmul1, hm_eta, heq_u, hfin_A, hA_rest]
    · have h4_gt : 1 < 4 * (y + 1 / 2) * η * t := lt_of_not_ge h4
      have h1e : 1 - Real.exp (-4 * (y + 1 / 2) * η * t) ≤ 1 := by
        linarith only [Real.exp_pos (-4 * (y + 1 / 2) * η * t)]
      have hmul1 : Real.exp (-em0) * (1 - Real.exp (-4 * (y + 1 / 2) * η * t)) ≤ Real.exp (-em0) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h1e (Real.exp_pos _).le
      have hsuff := gaussian_sum_ge_2a_big_gt hy hη0 hη_le ht h4_gt
      have hinv : Real.exp (-em0) ≤ 2 * η * (10 / 11 : ℝ) + A := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos em0)]
        dsimp [A, em0] at hsuff ⊢
        linarith only [hsuff]
      have hA_rest : 0 ≤ A ^ 2 / 2 + A ^ 3 / 6 := by positivity
      linarith only [hmul1, hinv, hA_rest]
  have hm0_le : Real.exp (-(y + 1 / 2 - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + η) ^ 2 * t) ≤
      (2 * η * (10 / 11 : ℝ) + A + A ^ 2 / 2 + A ^ 3 / 6) * Real.exp (-y ^ 2 * t) := by
    rw [hm0_fac]
    exact mul_le_mul_of_nonneg_right hcore (Real.exp_pos _).le
  have htsum_eq : ∑' m : ℕ, (Real.exp (-(y + 1 / 2 + m - η) ^ 2 * t) -
      Real.exp (-(y + 1 / 2 + m + η) ^ 2 * t)) =
      (Real.exp (-(y + 1 / 2 - η) ^ 2 * t) - Real.exp (-(y + 1 / 2 + η) ^ 2 * t)) +
      ∑' m : ℕ, (Real.exp (-((y + 1) + 1 / 2 + m - η) ^ 2 * t) -
        Real.exp (-((y + 1) + 1 / 2 + m + η) ^ 2 * t)) := by
    have hsp := hsplit.symm; dsimp only at hsp; rw [hsp, hsum1, htail_eq]
  linarith only [hlhs_ge, hm0_le, htail, htsum_eq]


lemma gaussian_sum_ge_aux {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (ht : 0 < t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by
  by_cases hδ_le : δ ≤ 1 / 4
  · exact RademacherGamma_gaussian_sum_ge_le_quarter hy hδ0 hδ_le ht
  · have hδ_gt14 : 1 / 4 < δ := lt_of_not_ge hδ_le
    set η := 1 / 2 - δ
    have hη0 : 0 < η := by dsimp [η]; linarith only [hδ1]
    have hη_le : η ≤ 1 / 4 := by dsimp [η]; linarith only [hδ_gt14]
    have hη12 : η < 1 / 2 := by linarith only [hη_le]
    have hδ_eq : δ = 1 / 2 - η := by dsimp [η]; ring
    rw [hδ_eq]
    by_cases h2b : 3 ≤ 2 * (y - η) ^ 2 * t
    · rcases case2_tsum_reindex y η t hη0 hη12 ht with ⟨_, hs2, hreidx⟩
      rw [hreidx]
      have hconv := gaussian_convex_tail_sum_le (a₀ := y) (by linarith only [hy, hη_le]) hη0 ht h2b
        (by simpa only [add_zero] using hs2)
      have hexp_cmp : Real.exp (-(y - η) ^ 2 * t) ≤ Real.exp (-(y - 1 / 2 + η) ^ 2 * t) := by
        apply Real.exp_le_exp.mpr
        have hdiff : (-(y - 1 / 2 + η) ^ 2 * t) - (-(y - η) ^ 2 * t) = (1 - 4 * η) * (y - 1 / 4) * t := by ring
        have hpos : 0 ≤ (1 - 4 * η) * (y - 1 / 4) * t := by
          have h1 : 0 ≤ 1 - 4 * η := by linarith only [hη_le]
          have h2 : 0 ≤ y - 1 / 4 := by linarith only [hy]
          positivity
        linarith only [hdiff, hpos]
      have hexp_ge2 : Real.exp (-y ^ 2 * t) ≤ Real.exp (-(y - η) ^ 2 * t) := by
        apply Real.exp_le_exp.mpr
        have h1 : (y - η) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by linarith only [hy, hη_le]) (by linarith only [hη0]) 2
        nlinarith only [h1, ht]
      have h12n : 0 ≤ 1 - 2 * η := by linarith only [hη_le]
      have h2η_nn : 0 ≤ 2 * η := by positivity
      have hm1 := mul_le_mul_of_nonneg_left hexp_ge2 h12n
      have hm2 := mul_le_mul_of_nonneg_left hexp_cmp h2η_nn
      linarith only [hconv, hexp_cmp, hm1, hm2,
        show 2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) = (1 - 2 * η) * Real.exp (-y ^ 2 * t) by ring]
    · have h2b_neg : 2 * (y - η) ^ 2 * t < 3 := lt_of_not_ge h2b
      by_cases ht710 : t ≤ 7 / 10
      · exact RademacherGamma_gaussian_sum_ge_2b_p3 hy hη0 hη_le ht ht710 h2b_neg
      · have ht_gt710 : 7 / 10 < t := lt_of_not_ge ht710
        by_cases ht4 : 4 ≤ t
        · exact gaussian_sum_ge_2a_big hy hη0 hη_le ht4
        · have ht_lt4 : t < 4 := lt_of_not_ge ht4
          have hy_le1810 : y ≤ 18 / 10 := by
            by_contra hy_gt1810; push Not at hy_gt1810
            have h1 : 31 / 20 ≤ y - η := by linarith only [hy_gt1810, hη_le]
            have h2 : 3 ≤ 2 * (y - η) ^ 2 * t := by nlinarith only [h1, ht_gt710]
            linarith only [h2, h2b_neg]
          exact RademacherGamma_gaussian_sum_ge_c2_box hy hy_le1810 hη0 hη_le ht_gt710 ht_lt4.le h2b_neg

end SolGammaHelpers

theorem solution {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (ht : 0 < t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) :=
  SolGammaHelpers.gaussian_sum_ge_aux hy hδ0 hδ1 ht
