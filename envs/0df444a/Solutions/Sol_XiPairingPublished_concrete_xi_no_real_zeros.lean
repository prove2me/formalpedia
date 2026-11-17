-- Prove2me | solution 1 for XiPairingPublished.concrete_xi_no_real_zeros
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:32:48.449091+00:00
-- url     : https://prove2.me/submissions/afffcb09-5721-466d-927e-7d91552d74ec

import Mathlib
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/ZetaFunctionalEquation.lean -/
section PntFile36
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
Completed zeta functional equation in product form.

We restate mathlib's completedRiemannZeta_one_sub as an equality of
(π^{-s/2} Γ(s/2) ζ(s)) with the corresponding (1-s) expression, matching
the form used by the ξ functional equation derivation.
-/

noncomputable section

section
open Complex

namespace Complex

/-- Functional equation for Mathlib's completed Riemann zeta factor `Λ`. -/
theorem zeta_functional_equation (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta (1 - s) := by
  simpa using (completedRiemannZeta_one_sub s).symm

/- Product-form functional equation matching `π^{−s/2} Γ(s/2) · ζ(s)` can be
   derived locally when needed via:
   `simpa [completedRiemannZeta, mul_comm, mul_left_comm, mul_assoc] using
     (completedRiemannZeta_one_sub s).symm`.
   Kept as a comment to avoid Hurwitz aliasing at call sites. -/

end Complex

end
end
end PntFile36


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/CompletedXi.lean -/
section PntFile37
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Local API for Mathlib's completed Riemann zeta and xi functions

This file records basic local facts about Mathlib's `completedRiemannZeta`

`Λ(s) = Γ_ℝ(s) * ζ(s)`.

It also defines the classical entire Riemann xi function
`ξ(s) = s * (s - 1) * Λ(s) / 2` via the pole-removed expression
`(s * (s - 1) * Λ₀(s) + 1) / 2`.  This is the object whose genus-one Hadamard product is used in
Kadiri-style zero-free region arguments.  This file only supplies the elementary bridge facts; the
Hadamard product is specialized in `Mathlib.NumberTheory.LSeries.RiemannZetaHadamard`, while the
xi logarithmic-derivative zero-sum bridge is also recorded there under explicit convergence,
nonvanishing, and point-not-a-zero hypotheses.

## References

* [kadiri2005] for the explicit zero-free-region context motivating the xi/log-derivative bridge
-/

section
noncomputable section

open Complex

namespace Complex

/-! ## The entire Riemann xi function -/

/-- The classical entire Riemann xi function, defined using the pole-removed completed zeta
function `Λ₀`.

Away from `0` and `1`, this agrees with `s * (s - 1) * completedRiemannZeta s / 2`; see
`riemannXi_eq_mul_completedRiemannZeta`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The normalization value `ξ(0) = 1 / 2`, immediate from the pole-removed definition. -/
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]

/-- The Riemann xi function is not identically zero. -/
theorem riemannXi_nontrivial : ∃ s : ℂ, riemannXi s ≠ 0 := by
  refine ⟨0, ?_⟩
  simp [riemannXi_zero]

/-- The Riemann xi function is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))).div_const 2

/-- Away from the poles of `completedRiemannZeta`, `riemannXi` is the classical product
`s * (s - 1) * completedRiemannZeta s / 2`. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [riemannXi, completedRiemannZeta_eq]
  have h1ms : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp [hs0, h1ms]
  ring

/-- Functional equation for the Riemann xi function. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

end Complex

end
end
end PntFile37


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Basic.lean -/
section PntFile38
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Elementary complex-analysis API

Small algebraic and metric lemmas for complex half-planes and basic rational expressions.
-/

section
namespace Complex

/-- If `z ≠ 1`, then `z / (z - 1) = 1 + (z - 1)⁻¹`. -/
theorem div_sub_one_eq_one_add_one_div (z : ℂ) (hz : z ≠ 1) : z / (z - 1) = 1 + (z - 1)⁻¹ := by
  have h : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  calc
    z / (z - 1) = ((z - 1) + 1) / (z - 1) := by ring_nf
    _ = (z - 1) / (z - 1) + 1 / (z - 1) := by rw [add_div]
    _ = 1 + (z - 1)⁻¹ := by simp [div_eq_mul_inv, h]

/-- A continuous complex-valued function is bounded on a closed ball. -/
lemma exists_norm_bound_on_closedBall {f : ℂ → ℂ} {R : ℝ}
    (hcont : ContinuousOn f (Metric.closedBall (0 : ℂ) R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ M := by
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  exact (hM z (Metric.mem_closedBall.mpr (by simpa using hz))).trans (le_max_left _ _)

/-- If `a < re z`, nested open balls around `z` stay in the half-plane `re · ≥ a`. -/
theorem exists_pos_radius_forall_mem_ball_re_ge {z₀ : ℂ} {a : ℝ} (ha : a < z₀.re) :
    ∃ δ > 0, ∀ (x y : ℂ), dist x z₀ < δ → dist y x < δ → a ≤ y.re := by
  set δ : ℝ := (z₀.re - a) / 2 with hδdef
  have hpos : 0 < z₀.re - a := sub_pos.mpr ha
  have hδpos : 0 < δ := by simpa [hδdef] using half_pos hpos
  refine ⟨δ, hδpos, ?_⟩
  intro x y hx hy
  have htri : dist y z₀ ≤ dist y x + dist x z₀ := dist_triangle y x z₀
  have hsumlt : dist y x + dist x z₀ < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - z₀‖ < δ + δ := by simpa [dist_eq_norm] using lt_of_le_of_lt htri hsumlt
  have hdeltaSum : δ + δ = z₀.re - a := by simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - z₀‖ < z₀.re - a := by simpa [hdeltaSum] using hnorm_lt
  have h_eps_lt : a < z₀.re - ‖y - z₀‖ := by
    have hsum' : a + ‖y - z₀‖ < z₀.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_left hnorm_lt_re a)
    simpa [lt_sub_iff_add_lt] using hsum'
  have hre_lower : -‖y - z₀‖ ≤ (y - z₀).re := (abs_le.mp (abs_re_le_norm (y - z₀))).1
  have hyge : z₀.re - ‖y - z₀‖ ≤ y.re := by
    have h' : z₀.re + (-‖y - z₀‖) ≤ z₀.re + (y - z₀).re := add_le_add_right hre_lower z₀.re
    have h'' : z₀.re + (y - z₀).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
  exact le_of_lt (lt_of_lt_of_le h_eps_lt hyge)

end Complex

end
end PntFile38


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Trigonometric.lean -/
section PntFile39
/-!
# Complex trigonometric bounds

Elementary exponential bounds for complex trigonometric functions.
-/

section
namespace Complex

/-- `‖cos z‖` is controlled by `exp |im z|`. -/
lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  have hcos :
      cos z = (exp (z * I) + exp (-z * I)) / 2 := by
    simp [cos]
  have htri :
      ‖exp (z * I) + exp (-z * I)‖ ≤ ‖exp (z * I)‖ + ‖exp (-z * I)‖ :=
    norm_add_le _ _
  have hdiv :
      ‖(exp (z * I) + exp (-z * I)) / 2‖
        ≤ (‖exp (z * I)‖ + ‖exp (-z * I)‖) / 2 := by
    have : ‖exp (z * I) + exp (-z * I)‖ / 2
          ≤ (‖exp (z * I)‖ + ‖exp (-z * I)‖) / 2 :=
      div_le_div_of_nonneg_right htri (by norm_num)
    simpa [Complex.norm_div, Complex.norm_ofNat] using this
  have h1 : ‖exp (z * I)‖ = Real.exp (-(z.im)) := by
    simp [norm_exp, mul_re, I_re, I_im]
  have h2 : ‖exp (-(z * I))‖ = Real.exp (z.im) := by
    simp [norm_exp, mul_re, I_re, I_im]
  have habs1 : Real.exp (-(z.im)) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs z.im)
  have habs2 : Real.exp (z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self z.im)
  have hsum :
      (‖exp (z * I)‖ + ‖exp (-(z * I))‖) / 2 ≤ Real.exp |z.im| := by
    have : ‖exp (z * I)‖ + ‖exp (-(z * I))‖
        ≤ Real.exp |z.im| + Real.exp |z.im| := by
      simpa [h1, h2] using add_le_add habs1 habs2
    have : (‖exp (z * I)‖ + ‖exp (-(z * I))‖) / 2
        ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 :=
      div_le_div_of_nonneg_right this (by norm_num)
    simpa [two_mul] using this
  have :
      ‖cos z‖ ≤ (‖exp (z * I)‖ + ‖exp (-(z * I))‖) / 2 := by
    simpa [hcos] using hdiv
  exact le_trans this hsum

end Complex

end
end PntFile39


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/IntegralBounds.lean -/
section PntFile40
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Gamma bounds from the Euler integral

Pointwise bounds for `Real.Gamma` and `Complex.Gamma` used in finite-order estimates for
completed zeta functions. These follow from the Euler integral representation and convexity on
`[1, 2]`, without Binet's kernel.

## Main results

* `Real.Gamma.le_one_of_mem_Icc` : `Γ(x) ≤ 1` for `x ∈ [1, 2]`
* `Complex.Gamma.norm_le_Gamma_re` : `‖Γ z‖ ≤ Γ (re z)` for `0 < re z`
* `Complex.Gamma.norm_le_one` : `‖Γ z‖ ≤ 1` for `1 ≤ re z ≤ 2`

## References

* [DLMF], §5.2.1 for the Euler integral representation
-/

open Real Complex Set MeasureTheory

section
noncomputable section

namespace Real
namespace Gamma

/-- For `x ∈ [1, 2]`, `Γ(x) ≤ 1` since `Γ(1) = Γ(2) = 1` and the function is convex. -/
theorem le_one_of_mem_Icc {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) : Gamma x ≤ 1 := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Gamma 1 = 1 := Gamma_one
  have h2 : Gamma 2 = 1 := Gamma_two
  let t := 2 - x
  have ht_nonneg : 0 ≤ t := by linarith
  have hx_conv : x = t * 1 + (1 - t) * 2 := by field_simp [t]; ring
  have := h_convex.2 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc
    Gamma x = Gamma (t * 1 + (1 - t) * 2) := by rw [hx_conv]
    _ ≤ t * Gamma 1 + (1 - t) * Gamma 2 := this
    _ = 1 := by rw [h1, h2]; ring

end Gamma
end Real

namespace Complex
namespace Gamma

/-- The Euler integral gives `‖Γ z‖ ≤ Γ (re z)` for `0 < re z`; compare [DLMF], §5.2.1. -/
theorem norm_le_Gamma_re {z : ℂ} (hz : 0 < z.re) : ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  have h_norm_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ = Real.exp (-t) * t ^ (z.re - 1) := by
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (z - 1)‖ = t ^ (z.re - 1) := by
      simpa using norm_cpow_eq_rpow_re_of_pos ht (z - 1)
    simp [norm_exp, hcpow]
  calc
    ‖GammaIntegral z‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ := by
          unfold GammaIntegral
          exact norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z.re - 1) := by
          exact setIntegral_congr_fun measurableSet_Ioi h_norm_eq

/-- For `1 ≤ re z ≤ 2`, `‖Γ z‖ ≤ 1`. -/
theorem norm_le_one {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) : ‖Gamma z‖ ≤ 1 := by
  have hz_pos : 0 < z.re := by linarith
  calc
    ‖Gamma z‖ ≤ Real.Gamma z.re := norm_le_Gamma_re hz_pos
    _ ≤ 1 := Real.Gamma.le_one_of_mem_Icc hlo hhi

/-- Squared form of `Complex.Gamma.norm_le_Gamma_re`. -/
theorem norm_sq_le_Gamma_re_sq {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ^ 2 ≤ (Real.Gamma z.re) ^ 2 := by
  have h := norm_le_Gamma_re hz
  have hΓ : 0 ≤ Real.Gamma z.re := (Real.Gamma_pos_of_pos hz).le
  simpa [pow_two] using mul_le_mul h h (norm_nonneg _) hΓ

/-- Squared comparison against the real-axis value at `re z`. -/
theorem norm_sq_le_norm_sq_Gamma_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖Gamma z‖ ^ 2 ≤ ‖Gamma z.re‖ ^ 2 := by
  have hz_pos : 0 < z.re := by linarith
  have h := norm_sq_le_Gamma_re_sq hz_pos
  have habs : ‖Gamma (z.re : ℂ)‖ = Real.Gamma z.re := by
    rw [Gamma_ofReal z.re, norm_real]
    exact abs_of_pos (Real.Gamma_pos_of_pos hz_pos)
  rw [habs]
  exact h

end Gamma
end Complex

end

end
end PntFile40


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/GammaBounds.lean -/
section PntFile41
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Bounds for `Complex.Gammaℝ`

Cauchy bounds for derivatives of Deligne's real Gamma factor.
-/

section
noncomputable section

open Complex Real Set Metric
open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

namespace Real
namespace Gamma

-- On `[1 / 2, 1]`, convexity bounds `Γ` by its value at `1 / 2`.
private lemma pnt41_le_Gamma_one_half {a : ℝ} (ha_low : 1 / 2 ≤ a) (ha_high : a ≤ 1) :
    Real.Gamma a ≤ Real.Gamma (1 / 2) := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h_half : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have h_sqrt_pi_gt_one : 1 < Real.sqrt Real.pi := by
    rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff (by aesop)]
    exact (by norm_num : (1 : ℝ) < 3).trans Real.pi_gt_three
  let t := 2 - 2 * a
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have ha_conv : a = t * (1 / 2) + (1 - t) * 1 := by
    field_simp [t]
    ring
  have hconv := h_convex.2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by linarith : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at hconv
  calc
    Real.Gamma a = Real.Gamma (t * (1 / 2) + (1 - t) * 1) := by rw [ha_conv]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma 1 := hconv
    _ = t * Real.Gamma (1 / 2) + (1 - t) * 1 := by rw [h1]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma (1 / 2) := by
      have hone : 1 ≤ Real.Gamma (1 / 2) := by
        rw [h_half]
        exact le_of_lt h_sqrt_pi_gt_one
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left
          (mul_le_mul_of_nonneg_left hone (sub_nonneg_of_le ht_le_one))
          (t * Real.Gamma (1 / 2))
    _ = Real.Gamma (1 / 2) := by ring

end Gamma
end Real

open Gamma Real

-- Tail bound for Euler's Gamma integral on `1 / 2 ≤ a ≤ 1`.
private lemma pnt41_integral_exp_neg_rpow_Ioi_one_le {a : ℝ}
    (ha_low : (1 / 2 : ℝ) ≤ a) (ha_high : a ≤ 1) :
    ∫ t in Ioi 1, Real.exp (-t) * t ^ (a - 1) ≤ Real.sqrt Real.pi := by
  have h_split :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) ∂volume) =
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) ∂volume) +
        (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1) ∂volume) := by
    have h_int_Ioc :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioc 0 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set Ioc_subset_Ioi_self
    have h_int_Ioi :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioi 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set (by
        intro x hx
        exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
          measurableSet_Ioi h_int_Ioc h_int_Ioi)
  have h_nonneg :
      (0 : ℝ) ≤ ∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc ?_
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht.1) _)
  have h_step₁ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
          (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) := by
    exact le_add_of_nonneg_right h_nonneg
  have h_step₂ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) =
        ∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) := by
    simpa [add_comm] using h_split.symm
  have h_step₃ :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1)) = Real.Gamma a := by
    simpa using (Real.Gamma_eq_integral (by linarith : 0 < a)).symm
  have h_le_Gamma :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma a := by
    have := h_step₁
    simpa [h_step₂, h_step₃] using this
  have h_tail :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma (1 / 2) :=
    h_le_Gamma.trans (Gamma.pnt41_le_Gamma_one_half ha_low ha_high)
  have hGammaHalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hGammaInv : Real.Gamma (2⁻¹) = Real.sqrt Real.pi := by
    simp_rw [inv_eq_one_div]
    aesop
  simpa [hGammaHalf, hGammaInv] using h_tail

private lemma pnt41_integral_rpow_Ioc_zero_one {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = 1 / s := by
  have h_eq : ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = ∫ t in (0)..(1), t ^ (s - 1) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  rw [h_eq]
  have hne : s - 1 ≠ -1 := by linarith
  have hlt : -1 < s - 1 := by linarith
  have h := (integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (h := Or.inl hlt))
  simp [one_rpow, zero_rpow hs.ne'] at h
  simp only [one_div, h]

namespace Complex
namespace Gamma

/-- If `0 < a ≤ re w ≤ 1`, then `‖Γ(w)‖ ≤ 1 / a + √π`. -/
lemma norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le {w : ℂ} {a : ℝ}
    (ha_pos : 0 < a) (hw : a ≤ w.re) (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  set f : ℝ → ℂ := fun t ↦ Complex.exp (-t) * t ^ (w - 1)
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (w.re - 1)
  have hw_pos : 0 < w.re := ha_pos.trans_le hw
  have hΓ : Complex.Gamma w = ∫ t in Ioi (0 : ℝ), f t := by
    rw [Complex.Gamma_eq_integral hw_pos]
    simp [Complex.GammaIntegral, f]
  have h_norm :
      ‖Complex.Gamma w‖ =
        ‖∫ t in Ioi (0 : ℝ), f t‖ := by
    simp [hΓ]
  have h_le_int :
      ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have h_int_real :
      ∫ t in Ioi (0 : ℝ), ‖f t‖
        = ∫ t in Ioi (0 : ℝ), g t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    simp [f, g, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos ht (w - 1)]
  have h_split :
      (∫ t in Ioi (0 : ℝ), g t)
        = (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
    have hIoc : IntegrableOn g (Ioc 0 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
    have hIoi : IntegrableOn g (Ioi 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := 0) (b := 1))
          measurableSet_Ioi hIoc hIoi)
  have h_ae_drop :
      (fun t : ℝ ↦ g t) ≤ᵐ[volume.restrict (Ioc 0 1)]
        (fun t : ℝ ↦ t ^ (w.re - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    have h_exp : Real.exp (-t) ≤ 1 := by
      have : (-t : ℝ) ≤ 0 := by linarith [ht.1]
      exact exp_le_one_iff.mpr this
    have h_nonneg : (0 : ℝ) ≤ t ^ (w.re - 1) :=
      Real.rpow_nonneg (le_of_lt ht.1) _
    simpa [g] using mul_le_of_le_one_left h_nonneg h_exp
  have hIoc₁ : IntegrableOn g (Ioc 0 1) :=
    (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
  have hIoc₂ : IntegrableOn (fun t : ℝ ↦ t ^ (w.re - 1)) (Ioc 0 1) := by
    have hInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (w.re - 1)) volume 0 1 := by
      simpa using
        intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < w.re - 1)
    simpa using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
          (a := 0) (b := 1) zero_le_one).1 hInt
  have h_drop_exp :
      (∫ t in Ioc 0 1, g t)
        ≤ ∫ t in Ioc 0 1, t ^ (w.re - 1) :=
    MeasureTheory.setIntegral_mono_ae_restrict hIoc₁ hIoc₂ h_ae_drop
  have h_big :
      ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := by
    have step1 : ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
      simpa [h_int_real, h_split] using h_le_int
    have step2 : (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t)
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) :=
      add_le_add_left h_drop_exp _
    simpa [h_norm] using (le_trans step1 step2)
  have h_Ioc_exact :
      ∫ t in Ioc 0 1, t ^ (w.re - 1) = 1 / w.re :=
    pnt41_integral_rpow_Ioc_zero_one hw_pos
  have h_tail :
      ∫ t in Ioi 1, g t ≤ Real.sqrt Real.pi := by
    by_cases hhalf : (1 / 2 : ℝ) ≤ w.re
    · have := pnt41_integral_exp_neg_rpow_Ioi_one_le hhalf hw_ub
      simpa [g] using this
    · have h_ae :
          (fun t : ℝ ↦ g t) ≤ᵐ[volume.restrict (Ioi 1)]
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) := by
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have hpow : t ^ (w.re - 1) ≤ t ^ ((1 / 2 : ℝ) - 1) := by
          have : w.re - 1 ≤ (1 / 2 : ℝ) - 1 := by linarith [hhalf]
          exact Real.rpow_le_rpow_of_exponent_le ht1 this
        have hnonneg : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
        simpa [g] using mul_le_mul_of_nonneg_left hpow hnonneg
      have hIntL : IntegrableOn g (Ioi 1) :=
        (Real.GammaIntegral_convergent hw_pos).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))
      have hIntR : IntegrableOn
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) (Ioi 1) :=
        (Real.GammaIntegral_convergent (by norm_num : 0 < (1 / 2 : ℝ))).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))
      have h_le : ∫ t in Ioi 1, g t
            ≤ ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1) :=
        MeasureTheory.setIntegral_mono_ae_restrict hIntL hIntR h_ae
      have h_upper :
          ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)
            ≤ Real.sqrt Real.pi := by
        have := pnt41_integral_exp_neg_rpow_Ioi_one_le
                  (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
                  (by norm_num : (1 / 2 : ℝ) ≤ (1 : ℝ))
        simpa using this
      exact h_le.trans h_upper
  have h_main :
      ‖Complex.Gamma w‖ ≤ 1 / w.re + Real.sqrt Real.pi := by
    calc
      ‖Complex.Gamma w‖
          ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := h_big
      _ = 1 / w.re + (∫ t in Ioi 1, g t) := by rw [h_Ioc_exact]
      _ ≤ 1 / w.re + Real.sqrt Real.pi := by exact add_le_add_right h_tail _
  have h_one_div : (1 / w.re : ℝ) ≤ 1 / a :=
    one_div_le_one_div_of_le ha_pos hw
  have : 1 / w.re + Real.sqrt Real.pi ≤ 1 / a + Real.sqrt Real.pi :=
    add_le_add_left h_one_div _
  exact h_main.trans this

end Gamma
end Complex

end

end
end PntFile41


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/GammaStirlingAux.lean -/
section PntFile42
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Auxiliary lemmas for Gamma strip bounds

This file contains the shared algebraic and geometric lemmas used to shift `Γ(s)` into a
vertical strip by the functional equation.

## References

* [DLMF], §5.11 for Stirling expansions around the Gamma function
* [whittakerWatson1927], Chapter XII for the classical Gamma-function background
* The functional equation Γ(z+1) = z·Γ(z) (Mathlib: `Complex.Gamma_add_one`)

## Main results

* `norm_sub_real_le`: subtracting a positive real smaller than `re s` does not increase `‖s‖`
* `prod_norm_le_pow`: the shifted Gamma product has norm at most `‖s‖ ^ m`
* `Gamma_iterate`: the iterated Gamma functional equation
-/

section
open Complex
open scoped Topology BigOperators

namespace Stirling.GammaAux

/-! ## Geometry of the shifted product -/

/-- If `0 < a < re s`, then subtracting `a` from `s` does not increase the norm. -/
lemma norm_sub_real_le {s : ℂ} {a : ℝ} (ha_pos : 0 < a) (ha_lt : a < s.re) : ‖s - a‖ ≤ ‖s‖ := by
  have h_sq : (s.re - a) ^ 2 ≤ s.re ^ 2 := by nlinarith
  have h1 : Complex.normSq (s - a) ≤ Complex.normSq s := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
               Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith [sq_nonneg s.im]
  calc
    ‖s - a‖ = Real.sqrt (Complex.normSq (s - a)) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (Complex.normSq s) := Real.sqrt_le_sqrt h1
    _ = ‖s‖ := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- For s : ℂ and k : ℕ with k + 1 < Re(s), we have |s - 1 - k| ≤ |s|. -/
lemma norm_shift_le {s : ℂ} {k : ℕ} (hk : (k : ℝ) + 1 < s.re) : ‖s - 1 - k‖ ≤ ‖s‖ := by
  have ha_pos : (0 : ℝ) < 1 + k := by linarith
  have ha_lt : (1 : ℝ) + k < s.re := by linarith
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    norm_sub_real_le (s := s) (a := (1 + k : ℝ)) ha_pos ha_lt

/-- Product bound: |∏_{k < m} (s-1-k)| ≤ |s|^m -/
lemma prod_norm_le_pow {s : ℂ} {m : ℕ} (h : ∀ k < m, (k : ℝ) + 1 < s.re) :
    ‖∏ k ∈ Finset.range m, (s - 1 - k)‖ ≤ ‖s‖ ^ m := by
  calc ‖∏ k ∈ Finset.range m, (s - 1 - k)‖
      = ∏ k ∈ Finset.range m, ‖s - 1 - k‖ := norm_prod _ _
    _ ≤ ∏ _k ∈ Finset.range m, ‖s‖ := by
        apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
        intro k hk; exact norm_shift_le (h k (Finset.mem_range.mp hk))
    _ = ‖s‖ ^ m := by rw [Finset.prod_const, Finset.card_range]

/-! ## Iterated functional equation -/

lemma Gamma_iterate {s : ℂ} {n : ℕ} (hs : ∀ k < n, s - 1 - k ≠ 0) :
    Complex.Gamma s = Complex.Gamma (s - n) * ∏ k ∈ Finset.range n, (s - 1 - k) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h_prev : ∀ k < m, s - 1 - k ≠ 0 := fun k hk => hs k (Nat.lt_succ_of_lt hk)
    have h_curr : s - 1 - m ≠ 0 := hs m (Nat.lt_succ_self m)
    have h_func : Complex.Gamma (s - m) = (s - m - 1) * Complex.Gamma (s - m - 1) := by
      have h_ne : s - ↑m - 1 ≠ 0 := by convert h_curr using 1; ring
      have := Complex.Gamma_add_one (s - m - 1) h_ne
      simp only [sub_add_cancel] at this
      exact this
    have h_cast : s - ↑(m + 1) = s - m - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    have h_prod_eq : (s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k) =
        ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
      rw [Finset.prod_range_succ]; ring
    calc
      Complex.Gamma s
          = Complex.Gamma (s - m) * ∏ k ∈ Finset.range m, (s - 1 - k) := ih h_prev
      _ = (s - m - 1) * Complex.Gamma (s - m - 1)
            * ∏ k ∈ Finset.range m, (s - 1 - k) := by
          rw [h_func]
      _ = Complex.Gamma (s - m - 1) *
            ((s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k)) := by
          ring
      _ = Complex.Gamma (s - m - 1) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
          rw [h_prod_eq]
      _ = Complex.Gamma (s - ↑(m + 1)) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
          rw [← h_cast]

end Stirling.GammaAux

end
end PntFile42


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/StripBounds.lean -/
section PntFile43
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Gamma bounds in half-planes

Bounds for `Complex.Gamma` and Deligne's real Gamma factor `Complex.Gammaℝ`, used
in finite-order estimates for completed zeta functions.
-/

section
noncomputable section

open Complex Real Set Metric


/-! ## Stirling-type bounds for the complex Gamma function

This section provides Stirling-type bounds on `Complex.Gamma` and the archimedean factor `Gammaℝ`
in regions of the complex plane that arise naturally in the analytic theory of
the completed zeta function, Hadamard factorization, and the Selberg class.
-/

namespace Real.Stirling

/-- For `x ≥ 1`, `log (1 + x) ≥ log 2`. -/
lemma log_one_add_ge_log_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ Real.log (1 + x) := by
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have hle : (2 : ℝ) ≤ 1 + x := by linarith
  exact Real.log_le_log h₂ hle

/-- For `x ≥ 1`, `log (1 + x) > 0`. -/
lemma log_one_add_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.log (1 + x) := Real.log_pos (by linarith)

/-- `√π < 2`. -/
lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le hπ4
    _ = 2 := h4

/-- For `x ≥ 1`, `log 2 ≤ x * log (1 + x)`. -/
lemma log_two_le_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ x * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_le := log_one_add_ge_log_two hx
  have hx_mul : x * Real.log 2 ≤ x * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left hlog2_le (by linarith)
  have hx_ge : Real.log 2 ≤ x * Real.log 2 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx hlog2_pos.le
  exact le_trans hx_ge hx_mul

/-- For `x ≥ 1`, `log 3 ≤ (log 3 / log 2) * log (1 + x)`. -/
lemma log_three_le_coef_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 3 ≤ (Real.log 3 / Real.log 2) * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 := div_nonneg hlog3_pos.le hlog2_pos.le
  have hscaled :
      (Real.log 3 / Real.log 2) * Real.log 2 ≤
        (Real.log 3 / Real.log 2) * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left (log_one_add_ge_log_two hx) hcoef_nonneg
  simpa [div_mul_cancel₀ _ hlog2_ne] using hscaled

/-- Absorbs the `s ↦ s/2 + 1` shift in half-plane Stirling bounds. -/
noncomputable def half_shift_log_constant : ℝ :=
  (3 / 2 : ℝ) * (Real.log 3 / Real.log 2 + 1)

lemma half_shift_log_constant_pos : 0 < half_shift_log_constant := by
  have hthree : 0 < (3 / 2 : ℝ) := by norm_num
  have hcoef : 0 < Real.log 3 / Real.log 2 + 1 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 :=
      div_nonneg hlog3_pos.le hlog2_pos.le
    linarith
  simpa [half_shift_log_constant] using mul_pos hthree hcoef

end Real.Stirling

namespace Complex.Gamma

open Real

/-- For `‖s‖ ≥ 1`, `‖s + 1‖ ≤ 2 * ‖s‖`. -/
lemma norm_add_one_le_two_mul_norm {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ ≤ 2 * ‖s‖ := by
  have h1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
  nlinarith [h1, hs]

/-- For `‖s‖ ≥ 1`, `‖s/2 + 1‖ ≤ (3/2) * ‖s‖`. -/
lemma norm_div_two_add_one_le_three_halves_mul {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ ≤ (3 / 2) * ‖s‖ := by
  have h1 : ‖s / 2 + 1‖ ≤ ‖s / 2‖ + 1 := by simpa using norm_add_le (s / 2) (1 : ℂ)
  have h1' : ‖s / 2 + 1‖ ≤ ‖s‖ / 2 + 1 := by simpa using h1
  nlinarith [h1', hs]

/-- For `‖s‖ ≥ 1`, `log(1 + ‖s + 1‖) ≤ log 2 + log(1 + ‖s‖)`. -/
lemma log_one_add_norm_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s + 1‖) ≤ Real.log 2 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s + 1‖ : ℝ) := by linarith [norm_nonneg (s + 1)]
  have hle : (1 + ‖s + 1‖ : ℝ) ≤ 2 * (1 + ‖s‖) := by
    have hn : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
    nlinarith [hn, hs]
  have hlog' : Real.log (1 + ‖s + 1‖) ≤ Real.log (2 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (2 * (1 + ‖s‖)) = Real.log 2 + Real.log (1 + ‖s‖) := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h2 h1
  simpa [hmul] using hlog'

/-- For `‖s‖ ≥ 1`, `log(1 + ‖s/2 + 1‖) ≤ log 3 + log(1 + ‖s‖)`. -/
lemma log_one_add_norm_div_two_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log 3 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s / 2 + 1‖ : ℝ) := by linarith [norm_nonneg (s / 2 + 1)]
  have hle : (1 + ‖s / 2 + 1‖ : ℝ) ≤ 3 * (1 + ‖s‖) := by
    nlinarith [norm_div_two_add_one_le_three_halves_mul hs]
  have hlog' : Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log (3 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (3 * (1 + ‖s‖)) = Real.log 3 + Real.log (1 + ‖s‖) := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h3 h1
  simpa [hmul] using hlog'

/-- For `‖s‖ ≥ 1`, the `s ↦ s + 1` shift in the Stirling exponent is absorbed by a factor `4`. -/
lemma norm_mul_log_shift_add_one_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖) ≤ 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog2_le := Real.Stirling.log_one_add_ge_log_two hs
  have hlog_add_le : Real.log (1 + ‖s + 1‖) ≤ 2 * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_add_one_le hs, hlog2_le]
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s + 1)])
  calc
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖)
        ≤ (2 * ‖s‖) * Real.log (1 + ‖s + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_add_one_le_two_mul_norm hs) hlog_nonneg
    _ ≤ (2 * ‖s‖) * (2 * Real.log (1 + ‖s‖)) :=
          mul_le_mul_of_nonneg_left hlog_add_le (by positivity)
    _ = 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by ring

/-- For `‖s‖ ≥ 1`, the `s ↦ s/2 + 1` shift in the half-plane Stirling exponent. -/
lemma norm_mul_log_shift_half_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
      Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s / 2 + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s / 2 + 1)])
  have hlog_w' :
      Real.log (1 + ‖s / 2 + 1‖) ≤
        (Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_div_two_add_one_le hs,
      Real.Stirling.log_three_le_coef_mul_log_one_add hs]
  calc
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)
        ≤ ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_div_two_add_one_le_three_halves_mul hs) hlog_nonneg
    _ ≤ Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
      have hstep2 :
          ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) ≤
            ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) :=
        mul_le_mul_of_nonneg_left hlog_w' (by positivity)
      have hEq :
          ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) =
            Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
        simp [Real.Stirling.half_shift_log_constant, mul_assoc, mul_left_comm, mul_comm]
      exact le_trans hstep2 (by simp [hEq])

/-- From `Γ(z + 1) = z Γ(z)` and `1/2 ≤ ‖z‖`, bound `‖Γ(z)‖` by `2 * ‖Γ(z + 1)‖`. -/
lemma norm_Gamma_le_two_mul_norm_Gamma_add_one {z : ℂ} (hz : z ≠ 0) (hz_lb : (1 / 2 : ℝ) ≤ ‖z‖) :
    ‖Gamma z‖ ≤ 2 * ‖Gamma (z + 1)‖ := by
  have hfunc := Gamma_add_one z hz
  have hnorm_mul : ‖Gamma (z + 1)‖ = ‖z‖ * ‖Gamma z‖ := by
    calc
      ‖Gamma (z + 1)‖ = ‖z * Gamma z‖ := by simp [hfunc]
      _ = ‖z‖ * ‖Gamma z‖ := by simp
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz_lb
  have hz_ne : ‖z‖ ≠ 0 := ne_of_gt hz_pos
  have h_inv : 1 / ‖z‖ ≤ (2 : ℝ) := by
    have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    simpa using one_div_le_one_div_of_le hhalf_pos hz_lb
  have : ‖Gamma z‖ = ‖Gamma (z + 1)‖ / ‖z‖ := by
    calc
      ‖Gamma z‖ = (‖z‖ * ‖Gamma z‖) / ‖z‖ := by field_simp [hz_ne]
      _ = ‖Gamma (z + 1)‖ / ‖z‖ := by simp [hnorm_mul]
  rw [this, div_eq_mul_inv]
  have :
      (‖Gamma (z + 1)‖ : ℝ) * (1 / ‖z‖) ≤ ‖Gamma (z + 1)‖ * 2 :=
    mul_le_mul_of_nonneg_left h_inv (norm_nonneg _)
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

/-- `Gamma` is bounded on any compact set that does not contain non-positive integers. -/
lemma norm_bounded_on_compact_of_no_poles {K : Set ℂ}
    (hK : IsCompact K)
    (h_poles : ∀ s ∈ K, ∀ n : ℕ, s ≠ -n) :
    ∃ M : ℝ, ∀ s ∈ K, ‖Gamma s‖ ≤ M := by
  have h_cont : ContinuousOn Gamma K := by
    refine continuousOn_of_forall_continuousAt ?_
    intro s hs
    exact (differentiableAt_Gamma s (h_poles s hs)).continuousAt
  rcases hK.exists_bound_of_continuousOn h_cont with ⟨M, hM⟩
  exact ⟨M, fun s hs => hM s hs⟩

/-- When `0 < a ≤ re w ≤ 1`, we have `‖Γ(w)‖ ≤ 1 / a + √π`. -/
theorem norm_le_strip {w : ℂ} {a : ℝ}
    (ha : 0 < a) (hw_lo : a ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi :=
  Complex.Gamma.norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le ha hw_lo hw_hi

/-- For `1/2 ≤ re w ≤ 1`, `‖Γ(w)‖ ≤ 4`. -/
lemma norm_le_four_of_re_half_to_one {w : ℂ}
    (hw_lo : (1 / 2 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 4 := by
  have h := norm_le_strip (w := w) (a := (1 / 2 : ℝ)) (by norm_num) hw_lo hw_hi
  calc ‖Gamma w‖ ≤ 1 / (1 / 2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 2 + 2 := by linarith [Real.Stirling.sqrt_pi_lt_two]
    _ = 4 := by norm_num

/-- For any `s : ℂ`, the real part of `s' := s - ⌊Re(s)⌋` lies in `[0, 1)`. -/
lemma floor_shift_re_in_strip {s : ℂ} :
    let s' := s - (⌊s.re⌋ : ℂ)
    0 ≤ s'.re ∧ s'.re < 1 := by
  intro s'
  have h₁ : 0 ≤ s.re - (⌊s.re⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have h₂ : s.re - (⌊s.re⌋ : ℝ) < 1 := by
    have h := Int.lt_floor_add_one (s.re)
    exact (sub_lt_iff_lt_add).mpr (by simp [add_comm])
  constructor
  · simp [s']
  · simpa [s'] using h₂

/-- For `re s ≥ 1`, `‖Γ(s)‖` is bounded by a polynomial in `‖s‖`. -/
theorem norm_bound_re_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖Gamma s‖ ≤ C * (1 + ‖s‖) ^ (‖s‖ + 1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro s hs_re
  classical
  by_cases hs_small : s.re < 2
  · -- On the strip `1 ≤ re s ≤ 2`, we have the sharp bound `‖Γ(s)‖ ≤ 1`.
    have hΓ : ‖Gamma s‖ ≤ 1 := Complex.Gamma.norm_le_one hs_re
      (le_of_lt hs_small)
    have hpow : (1 : ℝ) ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := by
      have hbase : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have hexp : (0 : ℝ) ≤ ‖s‖ + 1 := by linarith [norm_nonneg s]
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hexp
      simpa [Real.one_rpow] using h
    simpa [one_mul] using le_trans hΓ hpow
  · -- For `2 ≤ re s`, shift into `[1,2)` using the functional equation.
    have hs_ge_two : 2 ≤ s.re := le_of_not_gt hs_small
    let m : ℕ := ⌊s.re⌋₊ - 1
    have h_floor_ge2 : 2 ≤ ⌊s.re⌋₊ := Nat.le_floor (by exact_mod_cast hs_ge_two)
    have h_floor_le : (⌊s.re⌋₊ : ℝ) ≤ s.re := Nat.floor_le (by linarith : (0 : ℝ) ≤ s.re)
    have h_floor_gt : s.re < (⌊s.re⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one s.re)
    have hm_eq : (m : ℝ) = (⌊s.re⌋₊ : ℝ) - 1 := by
      have : (1 : ℕ) ≤ ⌊s.re⌋₊ := by omega
      simp [m, Nat.cast_sub this, Nat.cast_one]
    have hm_pos : 0 < m := by simp [m]; omega
    have h_re_lo : 1 ≤ (s - (m : ℂ)).re := by
      simp [sub_re, hm_eq]
      linarith [h_floor_le]
    have h_re_hi : (s - (m : ℂ)).re < 2 := by
      simp [sub_re, hm_eq]
      linarith [h_floor_gt]
    have h_k_bound : ∀ k < m, (k : ℝ) + 1 < s.re := by
      intro k hk
      calc (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.lt_iff_add_one_le.mp hk)
        _ = (⌊s.re⌋₊ : ℝ) - 1 := hm_eq
        _ < (⌊s.re⌋₊ : ℝ) := by linarith
        _ ≤ s.re := h_floor_le
    have prod_norm_le_pow :
        ‖∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ ≤ ‖s‖ ^ m := by
      simpa using Stirling.GammaAux.prod_norm_le_pow (s := s) (m := m) h_k_bound
    have Gamma_iterate :
        Gamma s = Gamma (s - (m : ℂ)) * ∏ k ∈ Finset.range m, (s - 1 - (k : ℂ)) := by
      have hs_nonzero : ∀ k < m, s - 1 - (k : ℂ) ≠ 0 := by
        intro k hk hk0
        have : (s - 1 - (k : ℂ)).re = 0 := by simp [hk0]
        have hk' : (k : ℝ) + 1 < s.re := h_k_bound k hk
        simp [Complex.sub_re] at this
        linarith
      simpa using Stirling.GammaAux.Gamma_iterate (s := s) (n := m) hs_nonzero
    have h_gamma_base : ‖Gamma (s - (m : ℂ))‖ ≤ 1 :=
      Complex.Gamma.norm_le_one h_re_lo (le_of_lt h_re_hi)
    have hΓ_le_pow : ‖Gamma s‖ ≤ ‖s‖ ^ m := by
      calc
        ‖Gamma s‖ =
            ‖Gamma (s - (m : ℂ)) * ∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ := by
              simp [Gamma_iterate]
        _ =
            ‖Gamma (s - (m : ℂ))‖ *
              ‖∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ := by
              simp
        _ ≤ 1 * ‖s‖ ^ m :=
            mul_le_mul h_gamma_base prod_norm_le_pow (norm_nonneg _) (by norm_num)
        _ = ‖s‖ ^ m := by ring
    have hm_le_norm : (m : ℝ) ≤ ‖s‖ := by
      have hm_le_floor : m ≤ ⌊s.re⌋₊ := Nat.sub_le _ _
      have hm_le_re : (m : ℝ) ≤ s.re := by
        have h_floor_le' : (⌊s.re⌋₊ : ℝ) ≤ s.re :=
          Nat.floor_le (by linarith : (0 : ℝ) ≤ s.re)
        exact le_trans (by exact_mod_cast hm_le_floor) h_floor_le'
      exact le_trans hm_le_re (Complex.re_le_norm s)
    have hpow_le : ‖s‖ ^ m ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := by
      have hx0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.cast_nonneg m)
      have hbase_le : ‖s‖ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have h1 : (‖s‖ : ℝ) ^ m = (‖s‖ : ℝ) ^ (m : ℝ) := by
        simp [Real.rpow_natCast]
      have h2 : (‖s‖ : ℝ) ^ (m : ℝ) ≤ (1 + ‖s‖) ^ (m : ℝ) :=
        Real.rpow_le_rpow hx0 hbase_le hm0
      have hbase1 : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have hm_le : (m : ℝ) ≤ ‖s‖ + 1 := by linarith [hm_le_norm]
      have h3 : (1 + ‖s‖) ^ (m : ℝ) ≤ (1 + ‖s‖) ^ (‖s‖ + 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase1 hm_le
      calc
        ‖s‖ ^ m = (‖s‖ : ℝ) ^ (m : ℝ) := h1
        _ ≤ (1 + ‖s‖) ^ (m : ℝ) := h2
        _ ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := h3
    have : ‖Gamma s‖ ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := le_trans hΓ_le_pow hpow_le
    simpa [one_mul] using this

/-- **Main Stirling bound** for `Re(s) ≥ 0`.

There exists a constant `C` such that for any `s` with `re s ≥ 0` and
`‖s‖ ≥ 1` we have `‖Γ(s)‖ ≤ exp (C · ‖s‖ · log (1 + ‖s‖))`. -/
theorem stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  classical
  rcases norm_bound_re_ge_one with ⟨C₁, hC₁_pos, hC₁⟩
  have hlog2_pos : 0 < Real.log 2 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos this
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  let K : ℝ := |Real.log C₁| + 1
  have hK_pos : 0 < K := by
    have : 0 ≤ |Real.log C₁| := abs_nonneg _
    linarith [K]
  have hC₁_exp : C₁ ≤ Real.exp K := by
    have hlog : Real.log C₁ ≤ |Real.log C₁| + 1 := by
      have : Real.log C₁ ≤ |Real.log C₁| := le_abs_self _
      linarith
    have h := Real.exp_le_exp.mpr hlog
    simpa [K, Real.exp_log hC₁_pos] using h
  let Cbase : ℝ := K / Real.log 2 + 2
  have hCbase_pos : 0 < Cbase := by
    have hK_div_nonneg : 0 ≤ K / Real.log 2 := div_nonneg hK_pos.le hlog2_pos.le
    linarith [Cbase, hK_div_nonneg]
  let C : ℝ := 4 * Cbase
  refine ⟨C, by nlinarith [hCbase_pos], ?_⟩
  have h_re_ge_one :
      ∀ z : ℂ, 1 ≤ z.re →
        ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) := by
    intro z hz_re
    have hz_norm : (1 : ℝ) ≤ ‖z‖ := le_trans hz_re (Complex.re_le_norm z)
    have hx_pos : 0 < (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
    have hL_nonneg : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have hlog2_le_log : Real.log 2 ≤ Real.log (1 + ‖z‖) :=
      Real.Stirling.log_one_add_ge_log_two hz_norm
    have hlog2_le : Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖) := by
      have hx_mul : ‖z‖ * Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left hlog2_le_log (by linarith)
      have hx_ge : Real.log 2 ≤ ‖z‖ * Real.log 2 := by
        have := mul_le_mul_of_nonneg_right hz_norm hlog2_pos.le
        simpa [one_mul] using this
      exact le_trans hx_ge hx_mul
    have hcoef_nonneg : 0 ≤ K / Real.log 2 := div_nonneg hK_pos.le hlog2_pos.le
    have hscaled :
        (K / Real.log 2) * Real.log 2 ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left hlog2_le hcoef_nonneg
    have hK_le : K ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
      have : (K / Real.log 2) * Real.log 2 = K := by field_simp [hlog2_ne]
      simpa [this] using hscaled
    have hlin :
        Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
          2 * (‖z‖ * Real.log (1 + ‖z‖)) := by
      have hz_le : ‖z‖ + 1 ≤ 2 * ‖z‖ := by linarith [hz_norm]
      have hmul :
          Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
            Real.log (1 + ‖z‖) * (2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left hz_le hL_nonneg
      -- rewrite
      simpa [mul_assoc, mul_left_comm, mul_comm, two_mul] using hmul
    -- Convert the polynomial bound into an exponential bound.
    have hpoly : ‖Gamma z‖ ≤ C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) := hC₁ z hz_re
    have hnonneg_rpow : 0 ≤ (1 + ‖z‖) ^ (‖z‖ + 1) :=
      Real.rpow_nonneg (by linarith [norm_nonneg z]) _
    have hmul :
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) ≤
          Real.exp K * (1 + ‖z‖) ^ (‖z‖ + 1) :=
      mul_le_mul_of_nonneg_right hC₁_exp hnonneg_rpow
    have hrpow :
        (1 + ‖z‖) ^ (‖z‖ + 1) =
          Real.exp (Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
      simp [Real.rpow_def_of_pos hx_pos, mul_comm]
    have hexp1 :
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) ≤
          Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
      calc
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1)
            ≤ Real.exp K * (1 + ‖z‖) ^ (‖z‖ + 1) := hmul
        _ = Real.exp K * Real.exp (Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by simp [hrpow]
        _ = Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
              simp [Real.exp_add]
    have hexp2 :
        Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1))
          ≤ Real.exp (Cbase * (‖z‖ * Real.log (1 + ‖z‖))) := by
      apply Real.exp_le_exp.mpr
      have hsum :
          K + Real.log (1 + ‖z‖) * (‖z‖ + 1)
            ≤ (K / Real.log 2 + 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
        -- split into the constant term and the rpow term
        have hK_term : K ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
          -- `‖z‖ * log(1+‖z‖)` is ≥ log 2, so we can scale
          -- (we already proved it with `hK_le`, but written with `‖z‖*log` instead of `log*‖z‖`)
          simpa [mul_assoc] using hK_le
        have h2_term :
            Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤ 2 * (‖z‖ * Real.log (1 + ‖z‖)) := hlin
        -- combine
        have :
            K + Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
              (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) +
                2 * (‖z‖ * Real.log (1 + ‖z‖)) := by
          nlinarith [hK_term, h2_term]
        -- factor
        simpa [Cbase, add_mul, mul_add, two_mul, mul_assoc, mul_left_comm, mul_comm] using this
      simpa [Cbase, mul_assoc] using hsum
    have hexp3 :
        Real.exp (Cbase * (‖z‖ * Real.log (1 + ‖z‖)))
          = Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) := by ring_nf
    have : ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) :=
      le_trans hpoly (le_trans hexp1 (le_trans hexp2 (by simp [hexp3] )))
    simpa [mul_assoc] using this
  intro s hs_re hs_norm
  have hs0 : s ≠ 0 := (norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  by_cases hs_ge_one : 1 ≤ s.re
  · have h1 := h_re_ge_one s hs_ge_one
    -- upgrade from `Cbase` to `C = 4*Cbase`
    have hmul_nonneg : 0 ≤ ‖s‖ * Real.log (1 + ‖s‖) := by
      have : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
      exact mul_nonneg (norm_nonneg _) this
    have hC_le : Cbase * (‖s‖ * Real.log (1 + ‖s‖)) ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
      have : Cbase ≤ C := by simp [C, le_mul_of_one_le_left, hCbase_pos.le]
      exact mul_le_mul_of_nonneg_right this hmul_nonneg
    have h2 : Real.exp (Cbase * ‖s‖ * Real.log (1 + ‖s‖))
        ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
      apply Real.exp_le_exp.mpr
      -- rewrite to use `hC_le`
      have hleft : Cbase * ‖s‖ * Real.log (1 + ‖s‖) = Cbase * (‖s‖ * Real.log (1 + ‖s‖)) := by ring
      have hright : C * ‖s‖ * Real.log (1 + ‖s‖) = C * (‖s‖ * Real.log (1 + ‖s‖)) := by ring
      -- `simp` both sides
      simpa [hleft, hright] using hC_le
    exact le_trans h1 h2
  · have hs_lt_one : s.re < 1 := lt_of_not_ge hs_ge_one
    -- relate `Γ(s)` to `Γ(s+1)` and bound using the `re≥1` case.
    have hnorm_eq : ‖Gamma s‖ = ‖Gamma (s + 1)‖ / ‖s‖ := by
      have h := Complex.Gamma_add_one s hs0
      have hn : ‖Gamma (s + 1)‖ = ‖s‖ * ‖Gamma s‖ := by
        calc
          ‖Gamma (s + 1)‖ = ‖s * Gamma s‖ := by simp [h]
          _ = ‖s‖ * ‖Gamma s‖ := by simp
      have hs_norm_ne : ‖s‖ ≠ 0 := (norm_ne_zero_iff).2 hs0
      calc
        ‖Gamma s‖ = (‖s‖ * ‖Gamma s‖) / ‖s‖ := by field_simp [hs_norm_ne]
        _ = ‖Gamma (s + 1)‖ / ‖s‖ := by simp [hn]
    have hdiv : ‖Gamma s‖ ≤ ‖Gamma (s + 1)‖ := by
      rw [hnorm_eq]
      exact div_le_self (norm_nonneg _) hs_norm
    have hs1 : (1 : ℝ) ≤ (s + 1).re := by
      -- `re(s+1) = re(s)+1`
      simp [Complex.add_re]
      linarith [hs_re]
    have hG1 : ‖Gamma (s + 1)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
      have h0 := h_re_ge_one (s + 1) hs1
      have hshift := norm_mul_log_shift_add_one_bound hs_norm
      have hC_nonneg : 0 ≤ Cbase := le_of_lt hCbase_pos
      have hCshift :
          Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖)) ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        calc
          Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖))
              ≤ Cbase * (4 * (‖s‖ * Real.log (1 + ‖s‖))) := by
                    exact mul_le_mul_of_nonneg_left hshift hC_nonneg
          _ = C * (‖s‖ * Real.log (1 + ‖s‖)) := by simp [C, mul_assoc, mul_left_comm, mul_comm]
      have h0' :
          Cbase * ‖s + 1‖ * Real.log (1 + ‖s + 1‖) =
            Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖)) := by
        ring
      have h1' :
          C * ‖s‖ * Real.log (1 + ‖s‖) =
            C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        ring
      exact le_trans h0 (by
        apply Real.exp_le_exp.mpr
        simpa [h0', h1'] using hCshift)
    exact le_trans hdiv hG1

/-- Stirling bound specialized to `Γ(s/2)` for `re s ≥ 0`. -/
theorem half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  classical
  rcases stirling_bound_re_ge_zero with ⟨C₀, hC₀_pos, hC₀⟩
  let A : ℝ := Real.Stirling.half_shift_log_constant
  have hA_pos := Real.Stirling.half_shift_log_constant_pos
  let C : ℝ := 1 + C₀ * A
  refine ⟨C, by nlinarith [hC₀_pos, hA_pos], ?_⟩
  intro s hs_re hs_norm
  have hs0 : s ≠ 0 := (norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  have hs2_neq : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num : (2 : ℂ) ≠ 0)
  have hs2_lb : (1 / 2 : ℝ) ≤ ‖s / 2‖ := by
    simpa using (show (1 / 2 : ℝ) ≤ ‖s‖ / 2 by nlinarith)
  have hdiv := norm_Gamma_le_two_mul_norm_Gamma_add_one hs2_neq hs2_lb
  have hz_re : 0 ≤ (s / 2 + 1).re := by simp [Complex.add_re]; linarith
  have hz_norm : (1 : ℝ) ≤ ‖s / 2 + 1‖ := by
    have : (1 : ℝ) ≤ (s / 2 + 1).re := by simp [Complex.add_re]; linarith
    exact le_trans this (Complex.re_le_norm (s / 2 + 1))
  have hΓz :
      ‖Gamma (s / 2 + 1)‖ ≤
        Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
    hC₀ (s / 2 + 1) hz_re hz_norm
  have hprod_w :
      ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤ A * (‖s‖ * Real.log (1 + ‖s‖)) := by
    simpa [A] using norm_mul_log_shift_half_bound hs_norm
  have hlog2_le_xlog := Real.Stirling.log_two_le_mul_log_one_add hs_norm
  -- Put everything together.
  have hmain :
      ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
    -- from `‖Γ(s/2)‖ ≤ 2‖Γ(s/2+1)‖`
    have htmp :
        ‖Gamma (s / 2)‖ ≤
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
      le_trans hdiv (mul_le_mul_of_nonneg_left hΓz (by norm_num))
    -- rewrite `2 = exp(log 2)`
    -- convert to a single exponential and compare exponents
    have htmp' :
        2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
          = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
      have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
        have : (0 : ℝ) < 2 := by norm_num
        simp [Real.exp_log this]
      -- `exp(log 2) * exp(A) = exp(log 2 + A)`
      calc
        2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            = Real.exp (Real.log 2) *
                Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
                simp [htwo, mul_assoc]
        _ = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
              simp [Real.exp_add]
    refine le_trans htmp (by
      -- compare exponents
      have hexp_le :
          Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)
            ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        have hC0_nonneg : 0 ≤ C₀ := le_of_lt hC₀_pos
        have hA_term :
            C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
              (C₀ * A) * (‖s‖ * Real.log (1 + ‖s‖)) := by
          -- use `hprod_w`
          have := mul_le_mul_of_nonneg_left hprod_w hC0_nonneg
          -- rearrange
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
        have hlog2_term : Real.log 2 ≤ 1 * (‖s‖ * Real.log (1 + ‖s‖)) := by
          simpa using hlog2_le_xlog
        -- combine and expand `C = 1 + C₀*A`
        nlinarith [hA_term, hlog2_term, C]
      -- apply exp monotonicity
      have h_exp :
          Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) :=
        Real.exp_le_exp.mpr hexp_le
      -- rewrite the left-hand side using `htmp'`
      have :
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) := by
        calc
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
              = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := htmp'
          _ ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) := h_exp
      simpa [mul_assoc] using this)
  -- final rewriting of the exponent
  simpa [mul_assoc] using hmain

end Complex.Gamma

namespace Complex.Gammaℝ.Stirling

open Real

/-- The norm of `π^{-s/2}` is at most `1` when `Re(s) ≥ 0`. -/
lemma norm_cpow_pi_neg_half_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi_pos]
  have h_re : (-s / 2).re = -s.re / 2 := by simp [Complex.neg_re]
  rw [h_re]
  have h_exp : -s.re / 2 ≤ 0 := by linarith
  have hpi_gt_1 : (1 : ℝ) < Real.pi := by
    calc (1 : ℝ) < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_gt_1) h_exp

/-- The norm of `(2π)^{-w}` is at most `1` when `Re(w) ≥ 0`. -/
lemma norm_cpow_two_mul_pi_neg_le_one {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1 := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by
    have : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    exact le_of_lt this
  have hnorm : ‖(2 * π : ℂ) ^ (-w)‖ = (2 * Real.pi) ^ ((-w : ℂ).re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := 2 * Real.pi) hbase_pos (-w)
  rw [hnorm]
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (neg_nonpos.mpr hw)

/-- **Stirling bound for the archimedean factor** `Γ_ℝ = π^{-s/2} · Γ(s/2)`. -/
theorem bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := Complex.Gamma.half_bound_re_ge_zero
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro s hs_re hs_norm
  have hdef : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    simp [Complex.Gammaℝ_def]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) :=
    hC₁ s hs_re hs_norm
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := norm_cpow_pi_neg_half_le_one hs_re
  have h1 : ‖Complex.Gammaℝ s‖ ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [hdef]; exact norm_mul_le _ _
  have h2 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := by
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * ‖Complex.Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ = ‖Complex.Gamma (s / 2)‖ := by ring
      _ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := hΓ
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hnorm_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
  have hC_le : C₁ * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C₁ + 2) * ‖s‖ * Real.log (1 + ‖s‖) := by
    apply mul_le_mul_of_nonneg_right _ hlog_nonneg
    apply mul_le_mul_of_nonneg_right _ hnorm_nonneg
    linarith
  exact le_trans (le_trans h1 h2) (Real.exp_le_exp.mpr hC_le)

/-- Finite order bound for Γ_ℝ. -/
theorem finite_order :
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (A * ‖s‖ ^ B) := by
  obtain ⟨C, hC_pos, hC⟩ := bound_re_ge_zero
  use C + 1, 2
  refine ⟨by linarith, by norm_num, ?_⟩
  intro s hs_re hs_norm
  have h := hC s hs_re hs_norm
  apply le_trans h
  apply Real.exp_le_exp.mpr
  -- log(1 + |s|) ≤ |s| for |s| ≥ 1, so C|s|log(1+|s|) ≤ C|s|² ≤ (C+1)|s|²
  have h_log : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    have h1 : 0 < 1 + ‖s‖ := by linarith [norm_nonneg s]
    have h2 : ‖s‖ + 1 ≤ Real.exp ‖s‖ := Real.add_one_le_exp ‖s‖
    have h2' : 1 + ‖s‖ ≤ Real.exp ‖s‖ := by linarith
    rw [Real.log_le_iff_le_exp (by linarith [norm_nonneg s])]
    exact h2'
  have step1 : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ C * ‖s‖ * ‖s‖ := by
    apply mul_le_mul_of_nonneg_left h_log
    apply mul_nonneg (by linarith) (norm_nonneg s)
  have step2 : C * ‖s‖ * ‖s‖ = C * ‖s‖ ^ 2 := by ring
  have step3 : C * ‖s‖ ^ 2 ≤ (C + 1) * ‖s‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h_combined : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C + 1) * ‖s‖ ^ 2 := by
    calc C * ‖s‖ * Real.log (1 + ‖s‖)
        ≤ C * ‖s‖ * ‖s‖ := step1
      _ = C * ‖s‖ ^ 2 := step2
      _ ≤ (C + 1) * ‖s‖ ^ 2 := step3
  -- Convert from ℕ exponent (^ 2) to ℝ exponent (^ (2 : ℝ))
  -- The goal is (C + 1) * ‖s‖ ^ (2 : ℝ), which equals (C + 1) * ‖s‖ ^ (2 : ℕ)
  -- This type coercion is handled by norm_cast
  have hconv : (C + 1) * ‖s‖ ^ 2 = (C + 1) * ‖s‖ ^ (2 : ℝ) := by norm_cast
  rw [← hconv]
  exact h_combined

end Complex.Gammaℝ.Stirling
end

end
end PntFile43


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean -/
section PntFile44
/-!
# Real-power estimates

Elementary logarithmic and real-power inequalities used in decay and growth estimates.
-/
section
namespace Real

/-- For `1 < u` and `ε > 0`, `log u * u^(-1-ε) ≤ (2/ε) * u^(-1-ε/2)`. -/
theorem log_mul_rpow_neg_le_two_div_mul_rpow_neg {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 < u) :
    Real.log u * u ^ (-1 - ε) ≤ (2 / ε) * u ^ (-1 - ε / 2) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hpos_coeff : 0 < 2 / ε := by
    simpa [one_div, div_eq_mul_inv] using mul_pos (by norm_num : (0 : ℝ) < 2) (inv_pos.mpr hε)
  have hle_exp : (ε / 2) * Real.log u ≤ Real.exp ((ε / 2) * Real.log u) :=
    le_trans (by linarith) (Real.add_one_le_exp ((ε / 2) * Real.log u))
  have hlog_bound : Real.log u ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) := by
    calc
      Real.log u = (2 / ε) * ((ε / 2) * Real.log u) := by field_simp [hεne]
      _ ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) :=
        mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
  have hexp_rpow : Real.exp ((ε / 2) * Real.log u) = u ^ (ε / 2) := by
    simp [Real.rpow_def_of_pos hu0, mul_comm]
  have hmul : Real.log u * u ^ (-1 - ε) ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) :=
    mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound)
      (le_of_lt (Real.rpow_pos_of_pos hu0 _))
  have hpow_mul : u ^ (ε / 2) * u ^ (-1 - ε) = u ^ (-1 - ε / 2) := by
    rw [← Real.rpow_add hu0, show ε / 2 + (-1 - ε) = -1 - ε / 2 by ring]
  calc
    Real.log u * u ^ (-1 - ε)
        ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) := hmul
    _ = (2 / ε) * u ^ (-1 - ε / 2) := by rw [mul_assoc, hpow_mul]

end Real

namespace Complex

/-- For `0 ≤ p`, one has `1 ≤ (1 + ‖z‖)^p`. -/
theorem one_le_one_add_norm_rpow (z : ℂ) {p : ℝ} (hp : 0 ≤ p) : (1 : ℝ) ≤ (1 + ‖z‖) ^ p :=
  Real.one_le_rpow (by linarith [norm_nonneg z]) hp

end Complex

end
end PntFile44


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZeta.lean -/
section PntFile45
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Extra Riemann zeta API

Vertical lines, prime-power bounds, and Euler-product identities supporting strip
and convexity bounds in `RiemannZetaConvexity`.

## Main results

* `verticalLine`, `verticalLine_re`, `verticalLine_add_const`
* `Nat.Primes.norm_one_sub_cpow_neg_vertical_le` and companions
* `riemannZeta_div_riemannZeta_eq_tprod_inv_one_add`, `norm_riemannZeta_div_riemannZeta`
* `norm_riemannZeta_eulerProduct`, `tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine`
-/

section
open scoped BigOperators Topology
open Complex Filter Real Set

/-- The point `σ + it` on the vertical line with real part `σ`. -/
def verticalLine (σ t : ℝ) : ℂ := σ + t * Complex.I

lemma verticalLine_re (σ t : ℝ) : (verticalLine σ t).re = σ := by
  simp only [verticalLine, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero]
  ring

lemma verticalLine_im (σ t : ℝ) : (verticalLine σ t).im = t := by
  simp only [verticalLine, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero]
  ring

lemma verticalLine_add_const (s : ℂ) (h t : ℝ) :
    s + (h : ℂ) + t * Complex.I = verticalLine (s.re + h) (s.im + t) := by
  apply Complex.ext
  · simp [verticalLine, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      add_assoc, add_comm]
  · simp [verticalLine, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, add_assoc, add_comm]

namespace Nat.Primes

/-- For a prime `p` and `s` with real part `> 1`, `‖p^{-s}‖ < 1`. -/
lemma norm_cpow_neg_lt_one (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s)
  have hz : -s.re < 0 := neg_lt_zero.mpr (lt_trans zero_lt_one hs)
  simpa [hnorm] using Real.rpow_lt_one_of_one_lt_of_neg hx1 hz

/-- `‖p^{-s}‖ = p^{- re s}` for a prime `p`. -/
lemma norm_cpow_neg_eq_rpow_neg_re (p : Nat.Primes) (s : ℂ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  have hx : 0 < ((p : ℕ) : ℝ) := Nat.cast_pos.mpr p.property.pos
  simpa [Complex.ofReal_natCast, Complex.neg_re] using
    Complex.norm_cpow_eq_rpow_re_of_pos hx (-s)

/-- `(p : ℝ)^(-r)` coerces to `(p : ℂ)^(-r)` for a prime `p` and real exponent `r`. -/
lemma cpow_neg_ofReal (p : Nat.Primes) (r : ℝ) :
    (((((p : ℕ) : ℝ) ^ (-r)) : ℝ) : ℂ) = ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)) := by
  have hp : 0 ≤ ((p : ℕ) : ℝ) := by positivity
  simpa using Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hp) (y := -r)

/-- `(1 + p^{-r})⁻¹` in `ℂ` equals the real inverse cast from `ℝ`. -/
lemma cast_inv_one_add (p : Nat.Primes) (r : ℝ) :
    ((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹) =
      (((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ : ℝ) : ℂ) := by
  calc
    ((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹)
        = ((1 + (((((p : ℕ) : ℝ) ^ (-r)) : ℝ) : ℂ))⁻¹) := by rw [← cpow_neg_ofReal p r]
    _ = (((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ : ℝ) : ℂ) := by
      simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]

lemma norm_cast_inv_one_add (p : Nat.Primes) (r : ℝ) :
    ‖((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹)‖ = (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  have hden : 0 ≤ 1 + ((p : ℕ) : ℝ) ^ (-r) := by positivity
  rw [cast_inv_one_add, Complex.norm_real]
  exact Real.norm_of_nonneg (inv_nonneg.mpr hden)

/-- On the vertical line `σ + it`, `‖1 - p^{-s}‖ ≤ 1 + p^{-σ}`. -/
lemma norm_one_sub_cpow_neg_vertical_le (p : Nat.Primes) (σ t : ℝ) :
    ‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖ ≤ 1 + ((p : ℕ) : ℝ) ^ (-σ) := by
  set s := verticalLine σ t
  have hre : s.re = σ := verticalLine_re σ t
  calc
    ‖1 - ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 + ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
      simpa [sub_eq_add_neg, norm_one, norm_neg] using
        norm_add_le (1 : ℂ) (-((p : ℕ) : ℂ) ^ (-s))
    _ = 1 + ((p : ℕ) : ℝ) ^ (-σ) := by rw [norm_cpow_neg_eq_rpow_neg_re, hre]

/-- On the vertical line `σ + it` with `1 < σ`, the Euler factor `1 - p^{-s}` is nonzero. -/
lemma one_sub_cpow_neg_vertical_ne_zero (p : Nat.Primes) (σ t : ℝ) (hσ : 1 < σ) :
    1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t) ≠ 0 := by
  intro h
  set s := verticalLine σ t
  have hs : 1 < s.re := by rw [verticalLine_re]; exact hσ
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-s) = 1 := by
    rw [sub_eq_zero] at h; exact h.symm
  have h_abs_lt : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := norm_cpow_neg_lt_one p s hs
  rw [hp_eq_one, show ‖(1 : ℂ)‖ = 1 from by simp] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

/-- Compare inverse Euler factors on the vertical line `σ + it` with `1 < σ`. -/
lemma inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical (p : Nat.Primes) (σ t : ℝ)
    (hσ : 1 < σ) :
    (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      (‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖)⁻¹ := by
  have hpos : 0 < ‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖ :=
    norm_pos_iff.mpr (one_sub_cpow_neg_vertical_ne_zero p σ t hσ)
  simpa [one_div] using one_div_le_one_div_of_le hpos (norm_one_sub_cpow_neg_vertical_le p σ t)

lemma multipliable_inv_one_add (r : ℝ) (hr : 1 < r) :
    Multipliable fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  have hsum : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-r) := by
    rw [Nat.Primes.summable_rpow]
    linarith
  have hlog : Summable fun p : Nat.Primes => Real.log (1 + ((p : ℕ) : ℝ) ^ (-r)) :=
    Real.summable_log_one_add_of_summable hsum
  exact Real.multipliable_of_summable_log (fun _ => by positivity)
    (by simpa [Real.log_inv, neg_mul] using hlog.neg)

lemma multipliable_complex_inv_one_add (r : ℝ) (hr : 1 < r) :
    Multipliable fun p : Nat.Primes => (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  have hu := multipliable_inv_one_add r hr
  have hmap := hu.map Complex.ofRealHom Complex.continuous_ofReal
  have h_eq :
      (fun p : Nat.Primes => (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹) =
        (fun x : ℝ => (x : ℂ)) ∘ fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
    funext p
    exact cast_inv_one_add p r
  simpa [h_eq, Function.comp_def] using hmap

/-- **`(1 - z²)⁻¹ = (1 - z)⁻¹ · (1 + z)⁻¹`** for `‖z‖ < 1`. -/
lemma inv_one_sub_sq_eq_mul_inv_one_sub_one_add (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z ^ 2)⁻¹ = (1 - z)⁻¹ * (1 + z)⁻¹ := by
  have hz0 : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    simp [this, norm_one] at hz
  have hz1 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by exact Eq.symm (neg_eq_of_add_eq_zero_right h)
    simp [this, norm_neg, norm_one] at hz
  calc
    (1 - z ^ 2)⁻¹ = ((1 - z) * (1 + z))⁻¹ := by ring
    _ = (1 + z)⁻¹ * (1 - z)⁻¹ := by simp [mul_inv_rev]
    _ = (1 - z)⁻¹ * (1 + z)⁻¹ := by ring

lemma eulerFactor_two_mul (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ =
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
  set z := ((p : ℕ) : ℂ) ^ (-s)
  have hz : ‖z‖ < 1 := norm_cpow_neg_lt_one p s hs
  have hpow : ((p : ℕ) : ℂ) ^ (-(2 * s)) = z ^ 2 := by
    simp only [z]
    rw [show -(2 * s) = (2 : ℂ) * (-s) by ring,
      show (2 : ℂ) * (-s) = ((2 : ℕ) : ℂ) * (-s) by norm_num, Complex.cpow_nat_mul]
  calc
    (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ = (1 - z ^ 2)⁻¹ := by rw [hpow]
    _ = (1 - z)⁻¹ * (1 + z)⁻¹ := inv_one_sub_sq_eq_mul_inv_one_sub_one_add z hz
    _ = (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by simp [z]

end Nat.Primes

section RiemannZetaEulerProduct

open Nat.Primes

/-- **`ζ(2r) = ζ(r) · ∏_p (1 + p^{-r})⁻¹`** for real `r > 1`. -/
theorem riemannZeta_eq_mul_tprod_inv_one_add (r : ℝ) (hr : 1 < r) :
    riemannZeta (2 * (r : ℂ)) =
      riemannZeta (r : ℂ) * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hs : 1 < s.re := by simpa [s] using hr
  have hs2 : 1 < (2 * s).re := by
    simp [s, Complex.mul_re, Complex.ofReal_re]
    linarith
  have hζ := (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hμ := multipliable_complex_inv_one_add r hr
  calc
    riemannZeta (2 * s)
        = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
          (riemannZeta_eulerProduct_tprod hs2).symm
    _ = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      refine tprod_congr fun p => eulerFactor_two_mul p s hs
    _ = (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) *
          ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [Multipliable.tprod_mul hζ hμ]
    _ = riemannZeta s * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [← riemannZeta_eulerProduct_tprod hs]

/-- **`ζ(2r)/ζ(r) = ∏_p (1 + p^{-r})⁻¹`** for real `r > 1`. -/
theorem riemannZeta_div_riemannZeta_eq_tprod_inv_one_add (r : ℝ) (hr : 1 < r) :
    riemannZeta (2 * (r : ℂ)) / riemannZeta (r : ℂ) =
      ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hs : 1 < s.re := by simpa [s] using hr
  have hzeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  calc
    riemannZeta (2 * s) / riemannZeta s
        = (riemannZeta s * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹) / riemannZeta s := by
          rw [riemannZeta_eq_mul_tprod_inv_one_add r hr]
    _ = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [mul_div_cancel_left₀ _ hzeta_ne]

theorem norm_riemannZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s‖ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
  calc
    ‖riemannZeta s‖ = ‖∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      rw [riemannZeta_eulerProduct_tprod hs]
    _ = ∏' p : Nat.Primes, ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      exact Multipliable.norm_tprod (riemannZeta_eulerProduct_hasProd hs).multipliable
    _ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
      congr 1; ext p; simp [norm_inv]

theorem norm_riemannZeta_div_riemannZeta (r : ℝ) (hr : 1 < r) :
    ‖riemannZeta (2 * (r : ℂ)) / riemannZeta (r : ℂ)‖ =
      ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hw := multipliable_complex_inv_one_add r hr
  calc
    ‖riemannZeta (2 * s) / riemannZeta s‖ = ‖∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      simpa [s] using congrArg norm (riemannZeta_div_riemannZeta_eq_tprod_inv_one_add r hr)
    _ = ∏' p : Nat.Primes, ‖(1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := Multipliable.norm_tprod hw
    _ = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
      refine tprod_congr fun p => norm_cast_inv_one_add p r

private lemma pnt45_multipliable_norm_eulerFactor_inv {ι : Type*} (g : ι → ℂ)
    (h : Multipliable fun i => (1 - g i)⁻¹) :
    Multipliable fun i => (‖1 - g i‖)⁻¹ := by
  simpa [norm_inv] using Multipliable.norm h

private lemma pnt45_hasProd_nonneg_of_pos {ι : Type*} (f : ι → ℝ) (hf₀ : ∀ i, 0 < f i) (a : ℝ)
    (ha : HasProd f a) : 0 ≤ a :=
  ge_of_tendsto ha <| Filter.Eventually.of_forall fun _ =>
    le_of_lt <| Finset.prod_pos fun i _ => hf₀ i

private lemma pnt45_hasProd_nnreal_of_coe {ι : Type*} (g : ι → NNReal) (b : NNReal)
    (h : HasProd (fun i => (g i : ℝ)) (b : ℝ)) : HasProd g b := by
  have h_eq : (fun s => ∏ i ∈ s, (g i : ℝ)) = fun s => ↑(∏ i ∈ s, g i) := by
    ext s; exact (NNReal.coe_prod s g).symm
  exact
    (NNReal.isEmbedding_coe.tendsto_nhds_iff.mpr <| by
      change Filter.Tendsto (fun s => ↑(∏ i ∈ s, g i)) Filter.atTop (𝓝 (b : ℝ))
      rw [← h_eq]
      exact h)

private lemma pnt45_multipliable_toNNReal {ι : Type*} (f : ι → ℝ) (hf₀ : ∀ i, 0 < f i)
    (hf : Multipliable f) : Multipliable fun i => (⟨f i, (hf₀ i).le⟩ : NNReal) := by
  obtain ⟨a, ha⟩ := hf
  let a_nnreal : NNReal := ⟨a, pnt45_hasProd_nonneg_of_pos f hf₀ a ha⟩
  exact ⟨a_nnreal, pnt45_hasProd_nnreal_of_coe _ _ (by simpa [a_nnreal] using! ha)⟩

private lemma pnt45_nnreal_coe_tprod {ι : Type*} (f : ι → NNReal) (hf : Multipliable f) :
    ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) :=
  (HasProd.map (Multipliable.hasProd hf) NNReal.toRealHom NNReal.continuous_coe).tprod_eq

private lemma pnt45_nnreal_tprod_le_coe {ι : Type*} (f g : ι → NNReal) (hf : Multipliable f)
    (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) :
    ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
  rw [pnt45_nnreal_coe_tprod f hf, pnt45_nnreal_coe_tprod g hg]
  exact NNReal.coe_le_coe.mpr h

/-- On the vertical line `re s = σ > 1`, the real product `∏_p (1 + p^{-σ})^{-1}` is dominated
by the Euler product at `σ + it`. -/
theorem tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine (σ t : ℝ) (hσ : 1 < σ) :
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ := by
  set s := verticalLine σ t
  have hs : 1 < s.re := by rw [verticalLine_re]; exact hσ
  have hf₀ : ∀ p : Nat.Primes, 0 < (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := fun _ => by positivity
  have hg₀ : ∀ p : Nat.Primes, 0 < (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := fun p =>
    inv_pos.mpr (norm_pos_iff.mpr (Nat.Primes.one_sub_cpow_neg_vertical_ne_zero p σ t hσ))
  let f : Nat.Primes → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹, (hf₀ p).le⟩
  let g : Nat.Primes → NNReal := fun p => ⟨(‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹, (hg₀ p).le⟩
  have hf := pnt45_multipliable_toNNReal _ hf₀ <| Nat.Primes.multipliable_inv_one_add σ hσ
  have hg := pnt45_multipliable_toNNReal _ hg₀ <|
    pnt45_multipliable_norm_eulerFactor_inv (g := fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s))
      (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hle : ∏' p, f p ≤ ∏' p, g p :=
    Multipliable.tprod_le_tprod (fun p =>
      Nat.Primes.inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical p σ t hσ) hf hg
  calc
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹
        = ∏' p, (f p : ℝ) := tprod_congr fun p => by unfold f; rfl
    _ ≤ ∏' p, (g p : ℝ) := pnt45_nnreal_tprod_le_coe f g hf hg hle
    _ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ :=
        tprod_congr fun p => by unfold g; rfl

end RiemannZetaEulerProduct

/-- `1 / (n : ℂ) ^ s` rewrites to `(n : ℂ) ^ (-s)` away from `n = 0`. -/
theorem one_div_natCast_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · simp [h, one_div, Complex.cpow_neg]

end


end PntFile45


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Convex.lean -/
section PntFile46
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Path-connected half-planes

This file proves that a right half-plane remains path-connected after removing one point.
The lemma is used to choose logarithms on punctured half-planes in complex-analysis arguments.
-/

section
namespace Complex

theorem isPathConnected_halfSpace_re_gt_diff_singleton (a : ℝ) (p : ℂ) (hp : a < p.re) :
    IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    · simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    · simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    · simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    · simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    · refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    · refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      · rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        · exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        · have hz_eq : z = p := by
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
              simp [heq, himeq]
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        · exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      · exact Or.inr (Or.inr hgt)
    · intro hz
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          · intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          · intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          · intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
  simpa [hcover] using hUnionPC


end Complex

end
end PntFile46


/- SOURCE PrimeNumberTheoremAnd/Mathlib/MeasureTheory/Integral/IntegrableOn.lean -/
section PntFile47
/-!
# Domination for `IntegrableOn`

A small `IntegrableOn` wrapper for a.e. norm domination on a restricted measure.
-/

section
namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {s : Set α}

/-- If `‖f x‖ ≤ g x` a.e. on `s` and `g` is integrable on `s`, then so is `f`. -/
lemma IntegrableOn.mono' {f : α → E} {g : α → ℝ} (hg : IntegrableOn g s μ)
    (hf : AEStronglyMeasurable f (μ.restrict s))
    (h : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ g x) : IntegrableOn f s μ := by
  exact Integrable.mono' hg hf h

end MeasureTheory

end
end PntFile47


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean -/
section PntFile48
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Improper-integral estimates

Elementary power-integral evaluations and convergence criteria for interval integrals on
half-lines.
-/

section
open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

theorem integral_interval_rpow_neg_one_sub {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    exact (not_le.mpr (lt_of_lt_of_le zero_lt_one hm)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by simpa [uIcc_of_le hmn] using h0notIcc
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    exact (ne_of_gt hε) (by linarith [h])
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    simpa using integral_rpow (a := m) (b := n) (r := -1 - ε) (Or.inr ⟨hrne, h0not⟩)
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := hint
    _ = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by ring

theorem integral_interval_rpow_neg_le {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  rw [integral_interval_rpow_neg_one_sub hε hm hmn, div_eq_mul_one_div, mul_comm]
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (le_trans zero_le_one (le_trans hm hmn)) _)

theorem intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (g : ℝ → ℝ) (c : ℝ)
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioi c)))
    (hbound : ∀ᵐ u ∂MeasureTheory.volume.restrict (Ioi c), ‖f u‖ ≤ g u)
    (hg : MeasureTheory.IntegrableOn g (Ioi c) MeasureTheory.volume) :
    Tendsto (fun N : ℕ => ∫ u in c..N, f u) atTop (𝓝 (∫ u in Ioi c, f u)) :=
  intervalIntegral_tendsto_integral_Ioi c (MeasureTheory.IntegrableOn.mono' hg hfm hbound)
    tendsto_natCast_atTop_atTop

/-- `∫_{1}^∞ u^{-re s - 1} = 1 / re s` for `0 < re s`. -/
theorem integral_Ioi_rpow_neg_re_sub_one {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp

end
end PntFile48


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Algebra/Order/Floor/Ring.lean -/
section PntFile49
/-!
# Floor and fractional-part estimates

Small floor-ring lemmas used by summation and Abel-continuation arguments.
-/

section
namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]

theorem fract_abs_le_one (a : R) : |fract a| ≤ 1 := by
  rw [abs_fract]
  exact (fract_lt_one a).le

end Int

end
end PntFile49


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean -/
section PntFile50
/-!
# Derivatives of complex powers

Derivative identities for functions of the form `w ↦ a * (u : ℂ) ^ (-w - 1)`.
-/
section
namespace Complex

/-- `(u : ℂ) ^ r` is continuous on `[a, b]` when `a > 0`. -/
theorem continuousOn_ofReal_cpow {r : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) :=
  (continuous_ofReal.continuousOn.cpow continuousOn_const
    (fun _ hu => (ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono Set.Subset.rfl

theorem deriv_ofReal_cpow_neg (s : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (fun (t : ℝ) => (t : ℂ) ^ (-s)) x = -s * (x : ℂ) ^ (-s - 1) := by
  by_cases hs : s = 0
  · simp [hs, deriv_const, cpow_zero, sub_eq_add_neg]
  · simpa [sub_eq_add_neg] using deriv_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

theorem continuousOn_deriv_ofReal_cpow_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (fun (t : ℝ) => (t : ℂ) ^ (-s))) (Set.Icc a b) :=
    ((continuousOn_const : ContinuousOn (fun (_ : ℝ) => (-s : ℂ)) (Set.Icc a b)).mul
      (continuousOn_ofReal_cpow (r := -s - 1) ha)).congr fun _ ht =>
    deriv_ofReal_cpow_neg s (lt_of_lt_of_le ha ht.1)

theorem ofReal_cpow_mul_cpow_neg_sub_one (s : ℂ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
  have hx : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  calc
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [cpow_one]
    _ = (u : ℂ) ^ (-s) := by rw [← cpow_add _ _ hx]; ring_nf

theorem natCast_mul_cpow_neg_eq_cpow_one_sub (N : ℕ) (s : ℂ) (hN : N ≠ 0) :
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 : ℂ) * (N : ℂ) ^ (-s) := by simp [cpow_one]
    _ = (N : ℂ) ^ (1 - s) := by rw [← cpow_add _ _ hN']; ring_nf

theorem HasDerivAt.const_mul_ofReal_cpow_neg_sub_one (a : ℂ) {u : ℝ} (hu : 0 < u) (z : ℂ) :
    HasDerivAt (fun w => a * (u : ℂ) ^ (-w - 1))
      (-a * (Complex.log u) * (u : ℂ) ^ (-z - 1)) z := by
  set huC : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hf : HasDerivAt (fun w => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id z).neg.sub_const (1 : ℂ)
  have hbase : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) hf (Or.inl huC)
  have hbase' : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (ofReal_log (x := u) (hx := le_of_lt hu))
  simpa [hlog, mul_comm, mul_left_comm, mul_assoc] using hbase'.const_mul a

end Complex

end
end PntFile50


/- SOURCE PrimeNumberTheoremAnd/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean -/
section PntFile51
/-!
# Interval-integral congruence lemmas

Congruence for interval integrals when the integrands agree on the oriented interval.
-/

section
open Set MeasureTheory

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ → E} {μ : Measure ℝ}

/-- If two functions agree on `Ioc a b`, their interval integrals agree. -/
theorem integral_congr_Ioc_of_le {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Ioc a b, f u = g u) :
    ∫ u in a..b, f u ∂μ = ∫ u in a..b, g u ∂μ := by
  refine integral_congr_ae' (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_) <;>
    intro u hu
  · exact h u hu
  · have hempty : Ioc b a = ∅ := Ioc_eq_empty hab.not_gt
    exact (hempty ▸ hu).elim

end intervalIntegral

end
end PntFile51


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelKernel.lean -/
section PntFile52
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Fractional-part kernel for the Abel zeta formula

`K_s(u) = {u} · u^{-s-1}` and its integrability / domination lemmas, used in
`RiemannZetaPartialSum` and `RiemannZetaAbelContinuation`.

## Main results

* `zetaAbelFractKernel`, `norm_zetaAbelFractKernel_le`
* `ZetaAbelFractKernel.intervalIntegrable`, `integrableOn_Ioi`, `tendsto_integral_Ioi`
* `ZetaAbelFractKernel.hasDerivAt_in_param`, `kernel_deriv_norm_bound_on_ball`
* `ZetaAbelFractKernel.integral_analytic`
-/

section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex

/-- Fractional-part kernel `{u} · u^{-s-1}` (`K_s` in the Abel formula). -/
noncomputable def zetaAbelFractKernel (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- `{u} · u^{-s-1}` is dominated by `u^{- re s - 1}` for `u ≥ 1`. -/
theorem norm_zetaAbelFractKernel_le (u : ℝ) (hu : 1 ≤ u) (s : ℂ) :
    ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hfract_le1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by simpa using Int.fract_abs_le_one u
  have hle : ‖zetaAbelFractKernel s u‖ ≤ ‖(u : ℂ) ^ (-s - 1)‖ := by
    calc
      _ = ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by rw [zetaAbelFractKernel, norm_mul]
      _ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        exact mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
      _ = ‖(u : ℂ) ^ (-s - 1)‖ := one_mul _
  have hb : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    have hre : (-s - 1).re = -s.re - 1 := by
      simp [sub_eq_add_neg]
    simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hu0 (-s - 1)
  exact hle.trans_eq hb

namespace ZetaAbelFractKernel

lemma aestronglyMeasurable (s : ℂ) (S : Set ℝ) (_ : MeasurableSet S) :
    AEStronglyMeasurable (fun u => zetaAbelFractKernel s u) (volume.restrict S) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)

lemma ae_bound_Ioi (s : ℂ) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) :=
  ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
    norm_zetaAbelFractKernel_le u (le_of_lt hu) s

lemma intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume a b := by
  let μ := volume.restrict (Icc a b)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
  have hmeas := aestronglyMeasurable s (Icc a b) measurableSet_Icc
  have hbound_ae : ∀ᵐ u ∂μ, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ ?_)
    intro u huIcc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos (ha.trans huIcc.1)
    have hg_eq : g u = u ^ (-s.re - 1) := by
      simp [g, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_eq_add_neg]
    exact (norm_zetaAbelFractKernel_le u (ha.trans huIcc.1) s).trans (le_of_eq hg_eq.symm)
  have hg : Integrable g μ := by
    simpa [μ, g] using!
      (Complex.continuousOn_ofReal_cpow (ha := one_pos.trans_le ha)).norm.integrableOn_compact
        isCompact_Icc
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    integrable_of_norm_sub_le hmeas hf0 hg
      (hbound_ae.mono fun u hu => by simpa [sub_eq_add_neg, μ, g] using hu)

theorem tendsto_integral_Ioi (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) :=
  intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le (f := fun u => zetaAbelFractKernel s u)
    (g := fun u => u ^ (-s.re - 1)) 1
    (aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi) (ae_bound_Ioi s)
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)

theorem integrableOn_Ioi (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun u => zetaAbelFractKernel s u) (volume.restrict (Ioi (1 : ℝ))) := by
  set ε : ℝ := s.re / 2
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
  have hfm := aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi
  have hε : 0 < ε := half_pos hs
  have hεle : ε ≤ s.re := half_le_self (le_of_lt hs)
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖zetaAbelFractKernel s u‖ ≤ g u :=
    ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
      (norm_zetaAbelFractKernel_le u (le_of_lt hu) s).trans
        (Real.rpow_le_rpow_of_exponent_le (le_of_lt hu) (by linarith [hεle]))
  simpa [IntegrableOn] using
    IntegrableOn.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) hfm hbound

lemma aestronglyMeasurable_param_deriv (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * zetaAbelFractKernel z u)
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hmeas : Measurable (fun u : ℝ => zetaAbelFractKernel z u) :=
    (measurable_fract.complex_ofReal.mul <| by simpa using Complex.measurable_ofReal.pow_const (-z - 1))
  simpa only [neg_mul] using
    (Real.measurable_log.complex_ofReal.fun_mul hmeas).fun_neg.aestronglyMeasurable

lemma eventually_aestronglyMeasurable_param (s : ℂ) :
    ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (fun u : ℝ => zetaAbelFractKernel z u) (volume.restrict (Ioi (1 : ℝ))) :=
  Eventually.of_forall fun z => aestronglyMeasurable z (Ioi (1 : ℝ)) measurableSet_Ioi

theorem hasDerivAt_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
    HasDerivAt (fun w => zetaAbelFractKernel w u)
      (-((Real.log u) : ℂ) * zetaAbelFractKernel z u) z := by
  have h := HasDerivAt.const_mul_ofReal_cpow_neg_sub_one ((Int.fract u : ℝ) : ℂ)
    (lt_trans zero_lt_one hu) z
  have hfun : (fun w => zetaAbelFractKernel w u) = fun w => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1) := by
    ext w; simp [zetaAbelFractKernel]
  exact (h.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by
    simp [zetaAbelFractKernel, Complex.ofReal_log (x := u) (hx := le_of_lt (lt_trans zero_lt_one hu)),
      mul_comm, mul_assoc, mul_left_comm])

theorem kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖ ≤ Real.log u * u ^ (-1 - ε) := by
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hinner : ‖zetaAbelFractKernel x u‖ ≤ u ^ (-1 - ε) :=
    (norm_zetaAbelFractKernel_le u hu1 x).trans (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  have hlognorm : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
  calc
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖
        = Real.log u * ‖zetaAbelFractKernel x u‖ := by rw [norm_mul, hlognorm]
    _ ≤ Real.log u * u ^ (-1 - ε) := mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.log_pos hu))

private lemma pnt52_ae_on_Ioi_of_all {p : ℝ → Prop} (h : ∀ u ∈ Ioi (1 : ℝ), p u) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), p u :=
  ae_restrict_iff' measurableSet_Ioi |>.2 (ae_of_all _ fun u hu => h u hu)

private lemma pnt52_dist_lt_of_mem_ball_half {z s : ℂ} {δ : ℝ} (hz : z ∈ Metric.ball s (δ / 2)) (hδ : 0 < δ) :
    dist z s < δ :=
  lt_trans (Metric.mem_ball.mp hz) (half_lt_self hδ)

/-- Dominated differentiation under `∫_{(1,∞)} F z`. -/
lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ) (hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ,
    HasDerivAt (fun w => F w u) (F' z u) z) :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (bound := bound) (Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint) (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  exact hDeriv

/-- `∫_{(1,∞)} K_z` is analytic in `z` for `re z > 0`. -/
theorem integral_analytic (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) s := by
  set ε : ℝ := s.re / 2
  have hεpos : 0 < ε := half_pos hs
  obtain ⟨δ, hδpos, hδprop⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge (z₀ := s) (a := ε) (half_lt_self hs)
  set F : ℂ → ℝ → ℂ := zetaAbelFractKernel
  set F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
  set bound : ℝ → ℝ := fun u => (2 / ε) * u ^ (-1 - ε / 2)
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [bound, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (by linarith [half_pos hεpos]) one_pos).const_mul (2 / ε)
  have hDiff : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s (half_pos hδpos)) ?_
    intro z hz
    set δ' : ℝ := δ / 2
    have hz_lt : dist z s < δ := pnt52_dist_lt_of_mem_ball_half hz hδpos
    have hRe : ∀ y ∈ Metric.ball z δ', ε ≤ y.re := fun y hy =>
      hδprop z y hz_lt (pnt52_dist_lt_of_mem_ball_half hy hδpos)
    have hzRe : ε ≤ z.re := hδprop s z (by simpa [dist_self] using hδpos) hz_lt
    exact (hasDerivAt_integral_param_dominated_Ioi F F' z δ' (half_pos hδpos)
      (eventually_aestronglyMeasurable_param z)
      (by simpa using integrableOn_Ioi z (lt_of_lt_of_le hεpos hzRe))
      (by simpa [F, F'] using aestronglyMeasurable_param_deriv z)
      bound hbound_int
      (pnt52_ae_on_Ioi_of_all fun u hu w hw =>
        (kernel_deriv_norm_bound_on_ball ε u hu w (hRe w hw)).trans
          (by simpa [bound] using Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hεpos hu))
      (pnt52_ae_on_Ioi_of_all fun u hu w hw => by simpa [F, F'] using hasDerivAt_in_param u hu w)).differentiableAt
  exact (Complex.analyticAt_iff_eventually_differentiableAt
    (f := fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u)).2 hDiff

end ZetaAbelFractKernel

end
end PntFile52


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/AbelSummation.lean -/
section PntFile53
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Finite-sum reindexing for Abel summation

Elementary reindexing lemmas for sums over initial intervals, used when passing between
floor sums and range sums.
-/

section
open Finset
open scoped BigOperators

variable {𝕜 : Type*} [AddCommGroup 𝕜]

/-- Reindex `∑ k ∈ Icc 1 N, f k` as `∑ n ∈ range N, f (n + 1)`. -/
theorem _root_.Finset.sum_Icc_one_eq_sum_range {N : ℕ} (f : ℕ → 𝕜) :
    ∑ k ∈ Icc 1 N, f k = ∑ n ∈ range N, f (n + 1) := by
  symm
  refine sum_bij (s := range N) (t := Icc 1 N)
    (f := fun n => f (n + 1)) (g := fun k => f k)
    (i := fun n _ => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := mem_range.mp hn
    exact mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le n), Nat.succ_le_of_lt hlt⟩
  · intro a ha b hb h
    exact Nat.succ_injective h
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, mem_range.mpr ?_, ?_⟩
    · have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (by simpa [hsucc] using hk2)
    · simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

/-- If `f 0 = 0`, the term at `0` in `Icc 0 N` is redundant. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_Icc_one {N : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  have hdecomp : insert 0 (Icc 1 N) = Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N)
  have hnotmem : (0 : ℕ) ∉ Icc 1 N := by
    intro h
    exact (not_le.mpr (Nat.lt_succ_self 0)) (mem_Icc.mp h).1
  calc
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ insert 0 (Icc 1 N), f k := by simp [hdecomp]
    _ = f 0 + ∑ k ∈ Icc 1 N, f k := by simp
    _ = ∑ k ∈ Icc 1 N, f k := by simp [h0]

/-- If `f 0 = 0`, summing over `Icc 0 m` equals summing `f (n + 1)` over `range m`. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_range_succ {m : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 m, f k = ∑ n ∈ range m, f (n + 1) := by
  rw [sum_Icc_zero_eq_sum_Icc_one h0, sum_Icc_one_eq_sum_range]

/-- Floor-summation reindexing for sequences with `c 0 = 0`. -/
theorem _root_.sum_Icc_zero_floor_eq_sum_range {c : ℕ → 𝕜} (hc0 : c 0 = 0) (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ n ∈ range ⌊t⌋₊, c (n + 1) :=
  Finset.sum_Icc_zero_eq_sum_range_succ (m := ⌊t⌋₊) (f := c) hc0

end
end PntFile53


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaPartialSum.lean -/
section PntFile54
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Abel-summation partial sums for the Riemann zeta function

For `re s > 1`, the partial Dirichlet sum `∑_{n<N} (n+1)^{-s}` satisfies the classical
Abel tail identity in `ZetaPartialSum.abel_formula`, and converges to `riemannZeta s`.

Used in `RiemannZetaAbelContinuation` to match the Abel integral formula for `re s > 1`.
-/

section
open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex Nat ZetaAbelFractKernel

/-- Partial sum of the Dirichlet series defining `ζ` for `re s > 1`. -/
noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

namespace ZetaPartialSum

private lemma pnt54_natCast_floor_eq_sub_fract (u : ℝ) (hu : 0 ≤ u) :
    (Nat.floor u : ℂ) = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by
  have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
    simpa using natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu
  have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hfloorR
  have hIFR : (Int.floor u : ℝ) = u - Int.fract u := (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)
  have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hIFR
  exact hfloorC.trans (by simpa [sub_eq_add_neg] using hIFC)

private lemma pnt54_intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn.mul
      (Complex.continuousOn_ofReal_cpow (r := -s - 1) (ha := one_pos.trans_le ha))
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
    (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2
    (hcont.integrableOn_compact isCompact_Icc)

private lemma pnt54_abel_summation (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
  have hle : (1 : ℝ) ≤ N := mod_cast hN
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t := fun t ht => by
    by_cases hs : s = 0; · simp [f, hs]
    simpa [f] using (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le zero_lt_one ht.1).ne'
      (neg_ne_zero.mpr hs)).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) (N : ℝ)) :=
    (Complex.continuousOn_deriv_ofReal_cpow_neg (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) zero_lt_one).integrableOn_compact
      isCompact_Icc
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c]) (hf_diff := hdiff) (hf_int := hint)
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
    rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
    simp [zetaPartialSum, f, c]
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    apply intervalIntegral.integral_congr_Ioc_of_le hle
    intro u hu
    rw [sum_Icc_zero_floor_eq_sum_range (hc0 := by simp [c]) u, Complex.deriv_ofReal_cpow_neg s (lt_trans zero_lt_one hu.1)]
    simp [c, Finset.sum_const, Finset.card_range, mul_comm, mul_left_comm]
  calc
    zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
          simpa [hLHS] using habel.trans (by rw [← intervalIntegral.integral_of_le hle])
    _ = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt_congr]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
            rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
            simp [c, f, Finset.sum_const, Finset.card_range, mul_comm]
          rw [hMain]; simp [f]

private lemma pnt54_abel_split (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  rw [pnt54_abel_summation s N hN]
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr_Ioc_of_le (mod_cast hN)]
    intro u _; simp [neg_mul, mul_left_comm]
  rw [hInt, sub_eq_add_neg, neg_mul, neg_neg]
  simp [Complex.natCast_mul_cpow_neg_eq_cpow_one_sub N s (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))]

private lemma pnt54_integral_split_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hab : (1 : ℝ) ≤ N := mod_cast hN
  have hI1 := pnt54_intervalIntegrable_mul_cpow_id s le_rfl hab
  have hI2 := ZetaAbelFractKernel.intervalIntegrable s le_rfl hab
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N, ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          simp [pnt54_natCast_floor_eq_sub_fract u (le_trans zero_le_one (le_of_lt hu.1)), sub_eq_add_neg]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          rw [← intervalIntegral.integral_sub hI1 hI2]
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u _; simp [sub_mul, zetaAbelFractKernel]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          congr 1
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          exact Complex.ofReal_cpow_mul_cpow_neg_sub_one (s := s) (hu := lt_trans zero_lt_one hu.1)

private lemma pnt54_cpow_integral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := mod_cast hN
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hrne : -s ≠ (-1 : ℂ) := fun h => hs (neg_inj.mp h)
    simpa using integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s)
      (Or.inr ⟨hrne, by simp [uIcc_of_le h01leN]⟩)
  calc s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
        simpa using congrArg (s * ·) hint
      _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
        rw [one_cpow, show (1 : ℂ) - s = -s + 1 from by ring]
      _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by field_simp

private lemma pnt54_abel_sub_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) := by
  rw [pnt54_abel_split s N hN, pnt54_integral_split_fract s N hN, mul_sub, add_sub_assoc]

/-- Abel tail formula for `re s > 1`. -/
theorem abel_formula (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hstep := pnt54_abel_sub_fract s N hN
  rw [pnt54_cpow_integral s hs N hN] at hstep
  let A := (N : ℂ) ^ (1 - s)
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) := by
    field_simp [sub_ne_zero.mpr hs, sub_ne_zero.mpr hs.symm]; ring
  rwa [halg] at hstep

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : (fun N : ℕ => (N : ℝ) ^ w.re) =ᶠ[atTop] fun N : ℕ => ‖(N : ℂ) ^ w‖ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Complex.norm_natCast_cpow_of_pos hN w]
  rw [tendsto_congr' (EventuallyEq.symm h1)]
  rw [show w.re = -(-w.re) from by ring]
  exact (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp tendsto_natCast_atTop_atTop

/-- `zetaPartialSum` converges to `riemannZeta` for `re s > 1`. -/
theorem tendsto_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using ne_of_gt this
  have hgSumm : Summable g := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hhSumm : Summable h := by
    have : Summable (fun n => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [Function.comp_apply, h, g] using this
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n, h n) = ∑' n, g n := by
    have : (∑' n, g n) = ∑' n, g (n + 1) := by simpa [hg0, add_comm] using Summable.tsum_eq_zero_add hgSumm
    simpa [h, g] using this.symm
  have hzeta : riemannZeta s = ∑' n, g n := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [zetaPartialSum, h, h_tsum_eq.trans hzeta.symm] using Summable.tendsto_sum_tsum_nat hhSumm

end ZetaPartialSum

end
end PntFile54


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelContinuation.lean -/
section PntFile55
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Abel-summation continuation of the Riemann zeta function

For `s ≠ 1` in the half-plane `{re s > σ₀}` with `σ₀ = 1/10`, the Riemann zeta function equals the
Abel-summation tail formula from [`Mathlib.NumberTheory.AbelSummation`]: writing `{u}` for the
fractional part of `u > 0` and `K_s(u) = {u} · u^{-s-1}`, one has

`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_{(1,∞)} K_s(u) du`.

The threshold `σ₀`, the domain, the kernel, and the renormalized integral are bundled in
`zetaAbelContinuationReLower`, `zetaAbelContinuationDomain`, `zetaAbelFractKernel`, and
`zetaAbelContinuationFormula`. The equality with `riemannZeta` on that domain is proved by analytic
continuation from `re s > 1`, where the formula is the classical Abel partial-sum limit.

Kernel and partial-sum input live in `RiemannZetaAbelKernel` and `RiemannZetaPartialSum`.

## Main results

* `zetaAbelContinuationDomain`, `zetaAbelContinuationFormula`
* `riemannZeta_eq_zetaAbelContinuationFormula`
* `norm_zetaAbelContinuationFormula_le`, `analyticOn_zetaAbelContinuationFormula`
-/

section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex ZetaPartialSum ZetaAbelFractKernel

/-- Lower threshold on `re s` for the Abel integral continuation of `ζ`. -/
noncomputable def zetaAbelContinuationReLower : ℝ := 1 / 10

theorem zetaAbelContinuationReLower_pos : 0 < zetaAbelContinuationReLower := by
  change 0 < (1 / 10 : ℝ)
  norm_num

theorem one_lt_zetaAbelContinuationReLower : zetaAbelContinuationReLower < (1 : ℝ) := by
  change (1 / 10 : ℝ) < 1
  norm_num

theorem one_sub_zetaAbelContinuationReLower :
    (1 - zetaAbelContinuationReLower : ℝ) = 9 / 10 := by
  change (1 - 1 / 10 : ℝ) = 9 / 10
  norm_num

theorem zetaAbelContinuationReLower_lt_half : zetaAbelContinuationReLower < (2⁻¹ : ℝ) := by
  change (1 / 10 : ℝ) < (2⁻¹ : ℝ)
  norm_num

/-- Domain `{s : ℂ | s ≠ 1 ∧ re s > 1/10}` where the Abel continuation of `ζ` is proved. -/
def zetaAbelContinuationDomain : Set ℂ :=
  {s | s ≠ (1 : ℂ) ∧ zetaAbelContinuationReLower < s.re}

theorem isOpen_zetaAbelContinuationDomain : IsOpen zetaAbelContinuationDomain := by
  change IsOpen ({s : ℂ | s ≠ 1} ∩ {s : ℂ | zetaAbelContinuationReLower < s.re})
  exact isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem isPreconnected_zetaAbelContinuationDomain : IsPreconnected zetaAbelContinuationDomain := by
  convert (Complex.isPathConnected_halfSpace_re_gt_diff_singleton
      (a := zetaAbelContinuationReLower) (p := (1 : ℂ)) one_lt_zetaAbelContinuationReLower).isConnected.isPreconnected using 1
  ext z; simp [zetaAbelContinuationDomain, and_comm]

theorem two_mem_zetaAbelContinuationDomain : (2 : ℂ) ∈ zetaAbelContinuationDomain := by
  refine ⟨by norm_num, ?_⟩
  change (1 / 10 : ℝ) < (2 : ℂ).re
  norm_num

theorem zetaAbelContinuationDomain_re_pos {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) :
    0 < s.re := lt_trans zetaAbelContinuationReLower_pos hs.2

theorem mem_zetaAbelContinuationDomain_of_re {s : ℂ} (hs_ne : s ≠ 1)
    (hs_re : zetaAbelContinuationReLower < s.re) : s ∈ zetaAbelContinuationDomain :=
  ⟨hs_ne, hs_re⟩

/-- On `zetaAbelContinuationDomain`, `‖z‖ / re z ≤ 10 * ‖z‖`. -/
theorem norm_div_re_le_ten_mul_norm_of_mem {z : ℂ} (hz : z ∈ zetaAbelContinuationDomain) :
    ‖z‖ / z.re ≤ 10 * ‖z‖ := by
  rw [div_eq_mul_inv, mul_comm]
  gcongr
  calc
    z.re⁻¹ = 1 / z.re := by rw [one_div]
    _ ≤ 1 / zetaAbelContinuationReLower :=
      one_div_le_one_div_of_le zetaAbelContinuationReLower_pos (le_of_lt hz.2)
    _ = 10 := by
      change (1 / (1 / 10 : ℝ)) = 10
      norm_num

/-- Abel renormalization `1 + (s-1)⁻¹ - s ∫_{(1,∞)} K_s`. -/
noncomputable def zetaAbelContinuationFormula (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u

theorem riemannZeta_abel_integral (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hsne : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by simp [h]
    linarith
  set G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N :=
    (eventually_ge_atTop 1).mono fun N hN => (abel_formula s hsne N hN).trans rfl
  have hG_to_zeta := (tendsto_congr' hEv).mp (tendsto_riemannZeta s hs)
  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Tendsto.const_mul (1 / (1 - s))
        (tendsto_natCast_cpow_zero_of_neg_re (1 - s)
          (by rw [Complex.sub_re, Complex.one_re]; linarith)))
  have hK : Tendsto (fun _ : ℕ => (1 + 1 / (s - 1) : ℂ)) atTop
      (𝓝 (1 + 1 / (s - 1))) := tendsto_const_nhds
  have hIntMul := (tendsto_integral_Ioi s hs).const_mul s
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 + 1 / (s - 1) : ℂ)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (1 + 1 / (s - 1))) := by
    simpa using! ((continuous_fst.add continuous_snd).tendsto _).comp (hA.prodMk_nhds hK)
  have hG_limit : Tendsto G atTop
      (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
    have hSub : Tendsto (fun N => Aseq N + Kseq N - Iseq N) atTop
        (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
      simpa [Function.comp_apply, Function.comp_def, sub_eq_add_neg] using
        ((continuous_fst.add continuous_snd).tendsto _).comp (hSum.prodMk_nhds hIntMul.neg)
    have hGdef : (fun N => Aseq N + Kseq N - Iseq N) = G := by
      funext N
      simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef] using hSub
  have huniq := tendsto_nhds_unique hG_to_zeta hG_limit
  simpa [zetaAbelContinuationFormula, sub_eq_add_neg] using huniq

/-- On `zetaAbelContinuationDomain`, the Abel formula satisfies the standard strip bound. -/
theorem norm_zetaAbelContinuationFormula_le (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    ‖zetaAbelContinuationFormula s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  let μ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
  have hs_re := zetaAbelContinuationDomain_re_pos hs
  have hint :
      ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ ‖s‖ / s.re :=
    mul_le_mul_of_nonneg_left
      ((MeasureTheory.norm_integral_le_of_norm_le (μ := μ)
        (f := fun u => zetaAbelFractKernel s u) (g := g)
        (by
          simpa [μ, g, IntegrableOn] using
            (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos))
        (by
          refine (ae_restrict_iff' measurableSet_Ioi).2 (MeasureTheory.ae_of_all _ ?_)
          intro u hu
          simpa [g] using norm_zetaAbelFractKernel_le u (le_of_lt hu) s)).trans
        (by simpa [μ, g, one_div] using
          (le_of_eq (by simp [integral_Ioi_rpow_neg_re_sub_one (s := s) hs_re]))))
      (norm_nonneg s)
  have hsplit :
      ‖zetaAbelContinuationFormula s‖ ≤
        1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
    simp only [zetaAbelContinuationFormula, one_div]
    calc
      ‖1 + (s - 1)⁻¹ - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖
          ≤ ‖1 + (s - 1)⁻¹‖ + ‖-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le (1 + (s - 1)⁻¹) (-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)
      _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
        gcongr
        · simpa [norm_one] using norm_add_le (1 : ℂ) ((s - 1)⁻¹)
        · exact (norm_mul_le (-s) (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)).trans_eq
            (by rw [norm_neg])
  calc
    ‖zetaAbelContinuationFormula s‖
        ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := hsplit
    _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re := add_le_add_right hint _
    _ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by simp [one_div]

/-- The Abel continuation formula is analytic on `zetaAbelContinuationDomain`. -/
theorem analyticOn_zetaAbelContinuationFormula :
    AnalyticOn ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
  simp only [AnalyticOn, zetaAbelContinuationDomain, Set.mem_ofPred_eq]
  intro s ⟨hs_ne, hs_re⟩
  apply AnalyticAt.analyticWithinAt
  refine analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_) |>.sub
    (analyticAt_id.mul (integral_analytic s (lt_trans zetaAbelContinuationReLower_pos hs_re)))
  exact sub_ne_zero.mpr hs_ne

/-- The Abel integral formula agrees with `ζ` on `zetaAbelContinuationDomain`. -/
theorem riemannZeta_eq_zetaAbelContinuationFormula (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hUo := isOpen_zetaAbelContinuationDomain
  have hζ : AnalyticOnNhd ℂ riemannZeta zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    have h : AnalyticOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
      isOpen_compl_singleton.analyticOn_iff_analyticOnNhd.mpr analyticOn_riemannZeta
    exact AnalyticOn.mono h fun _ hz => hz.1
  have hF : AnalyticOnNhd ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact analyticOn_zetaAbelContinuationFormula
  have hEq : riemannZeta =ᶠ[𝓝 (2 : ℂ)] zetaAbelContinuationFormula := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
      using riemannZeta_abel_integral w hw
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hζ hF isPreconnected_zetaAbelContinuationDomain two_mem_zetaAbelContinuationDomain hEq) hs

end
end PntFile55



namespace XiRealAxis
open Complex Set MeasureTheory

theorem zeta_re_neg (x : ℝ) (hx : 1/2 ≤ x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  have hx0 : 0 < x := by linarith
  have hInt := ZetaAbelFractKernel.integrableOn_Ioi (x : ℂ) (by simpa using hx0)
  have hnonneg : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      0 ≤ (zetaAbelFractKernel (x : ℂ) u).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_trans zero_le_one (le_of_lt hu)
    have hp : (u : ℂ)^(-(x : ℂ)-1) = ((u^(-x-1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hu0]
      congr 1 <;> push_cast <;> ring
    rw [zetaAbelFractKernel, hp]
    simpa using mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg hu0 _)
  have hi : 0 ≤ (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (x : ℂ) u).re := by
    have heq : (∫ u in Ioi (1 : ℝ), (zetaAbelFractKernel (x : ℂ) u).re) =
        (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (x : ℂ) u).re := integral_re hInt
    rw [← heq]
    exact integral_nonneg_of_ae hnonneg
  have hs : (x : ℂ) ∈ zetaAbelContinuationDomain := by
    constructor
    · exact_mod_cast (ne_of_lt hx1)
    · change (1/10 : ℝ) < x
      linarith
  have h := congrArg Complex.re (riemannZeta_eq_zetaAbelContinuationFormula (x : ℂ) hs)
  have he : (x : ℂ)-1 = ((x-1 : ℝ) : ℂ) := by push_cast; rfl
  simp only [zetaAbelContinuationFormula, he, Complex.add_re, Complex.sub_re,
    Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  have hc : (1 / ((x-1 : ℝ) : ℂ)).re = 1/(x-1) := by
    norm_cast
  rw [hc] at h
  have hn : 1 + (x-1)⁻¹ < 0 := by
    have hd : x-1 < 0 := by linarith
    have heq : 1 + (x-1)⁻¹ = x/(x-1) := by
      field_simp [ne_of_lt hd]
      ring
    rw [heq]
    exact div_neg_of_pos_of_neg hx0 hd
  have hm := mul_nonneg hx0.le hi
  simp only [one_div] at h
  linarith

theorem xi_real_ne_zero (x : ℝ) : Complex.riemannXi (x : ℂ) ≠ 0 := by
  have upper (y : ℝ) (hy : 1/2 ≤ y) : Complex.riemannXi (y : ℂ) ≠ 0 := by
    by_cases hy1 : y = 1
    · subst y
      norm_num [Complex.riemannXi]
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by linarith)
    have hy1c : (y : ℂ) ≠ 1 := by exact_mod_cast hy1
    have hz : riemannZeta (y : ℂ) ≠ 0 := by
      rcases lt_or_gt_of_ne hy1 with hlt | hgt
      · intro h
        have hh := zeta_re_neg y hy hlt
        simp [h] at hh
      · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hgt.le)
    have hc : completedRiemannZeta (y : ℂ) ≠ 0 := by
      intro h
      apply hz
      rw [riemannZeta_def_of_ne_zero hy0, h, zero_div]
    rw [Complex.riemannXi_eq_mul_completedRiemannZeta hy0 hy1c]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hy0 (sub_ne_zero.mpr hy1c)) hc) (by norm_num)
  by_cases hx : 1/2 ≤ x
  · exact upper x hx
  · have hu := upper (1-x) (by linarith : 1/2 ≤ 1-x)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.riemannXi_one_sub] using hu

end XiRealAxis

theorem solution (x : ℝ) :
    (((x : ℂ)*((x : ℂ)-1)*completedRiemannZeta₀ (x : ℂ)+1)/2) ≠ 0 :=
  XiRealAxis.xi_real_ne_zero x
#print axioms solution
