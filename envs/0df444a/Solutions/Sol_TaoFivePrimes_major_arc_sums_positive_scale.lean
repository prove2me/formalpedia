-- Prove2me | solution 1 for TaoFivePrimes.major_arc_sums_positive_scale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:33:58.020062+00:00
-- url     : https://prove2.me/submissions/d46532b2-ad44-4612-b77a-d6f3d737bf02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_TaoFivePrimes_riemann_verified_finite_and_count
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_TaoFivePrimes_vonMangoldt_explicit_formula
import Theorems.Thm_TaoFivePrimes_prop72_zero_series_remainder_bound
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

-- Step 1: `mathlib_riemannHypothesis` implies `TaoFivePrimes.riemann_verified` (accepted reduction of `TaoFivePrimes.riemann_verified`).
section

namespace TaoFivePrimes
end TaoFivePrimes
open TaoFivePrimes
theorem TaoFivePrimes.riemann_verified :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 ≤ s.im →
        s.im ≤ 3.29 * 10 ^ 9 → s.re = 1 / 2) ∧
      {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
        s.im ≤ 3.29 * 10 ^ 9}.Finite ∧
      {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
        s.im ≤ 3.29 * 10 ^ 9}.ncard ≤ 10 ^ 10 :=
  ⟨fun s hz h0 h1 _ _ =>
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis s hz h0 h1,
    TaoFivePrimes.riemann_verified_finite_and_count⟩

end

-- Step 2: `TaoFivePrimes.riemann_verified` implies `TaoFivePrimes.major_arc_sums_positive_scale` (accepted reduction of `TaoFivePrimes.major_arc_sums_positive_scale`).
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology

namespace TaoFivePrimes.Prop71Bridge

private noncomputable def weighted (eta : ℝ → ℝ) (x alpha u : ℝ) : ℂ :=
  (eta (u / x) : ℂ) * expCircle (alpha * u)

private theorem weighted_smooth (eta : ℝ → ℝ) (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (x alpha : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (weighted eta x alpha) := by
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (fun u => (eta (u / x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (heta.comp (contDiff_id.div_const x))
  have hphase : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => expCircle (alpha * u)) := by
    unfold expCircle
    have harg : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ((alpha * u : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_const (c := alpha)).mul contDiff_id)
    exact ((contDiff_const (c := (2 * Real.pi * Complex.I : ℂ))).mul harg).cexp
  exact hcut.mul hphase

private theorem weighted_support (eta : ℝ → ℝ) (c c' x alpha : ℝ) (hx : 0 < x)
    (hsupp : ∀ u, eta u ≠ 0 → u ∈ Icc c c') :
    Function.support (weighted eta x alpha) ⊆ Icc (c * x) (c' * x) := by
  intro u hu
  have he : eta (u / x) ≠ 0 := by intro h; exact hu (by simp [weighted, h])
  obtain ⟨hl, hh⟩ := hsupp _ he
  exact ⟨(le_div_iff₀ hx).mp hl, (div_le_iff₀ hx).mp hh⟩

private theorem weighted_compact (eta : ℝ → ℝ) (c c' x alpha : ℝ) (hx : 0 < x)
    (hsupp : ∀ u, eta u ≠ 0 → u ∈ Icc c c') :
    HasCompactSupport (weighted eta x alpha) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (weighted_support eta c c' x alpha hx hsupp)

private theorem correction_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hsupp : ∀ u, f u ≠ 0 → 2 ≤ u) :
    Integrable (fun u : ℝ => f u / ((u ^ 3 - u : ℝ) : ℂ)) := by
  have hcomp : HasCompactSupport (fun u : ℝ => f u / ((u ^ 3 - u : ℝ) : ℂ)) := by
    have he : (fun u : ℝ => f u / ((u ^ 3 - u : ℝ) : ℂ)) =
        f * (fun u : ℝ => (((u ^ 3 - u : ℝ) : ℂ))⁻¹) := by
      funext u; exact div_eq_mul_inv _ _
    rw [he]
    exact hc.mul_right
  have hcont : Continuous (fun u : ℝ => f u / ((u ^ 3 - u : ℝ) : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u < 2
    · have he : (fun u : ℝ => f u / ((u ^ 3 - u : ℝ) : ℂ)) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hu] with v hv
        have hvf : f v = 0 := by
          by_contra hn
          exact (not_lt.mpr (hsupp _ hn)) hv
        simp [hvf]
      exact continuousAt_const.congr_of_eventuallyEq he
    · have hup : 2 ≤ u := not_lt.mp hu
      have hd : ((u ^ 3 - u : ℝ) : ℂ) ≠ 0 := by
        apply Complex.ofReal_ne_zero.mpr
        rw [show u ^ 3 - u = u * (u - 1) * (u + 1) by ring]
        exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)
      exact hf.continuousAt.div (by fun_prop) hd
  exact hcont.integrable_of_hasCompactSupport hcomp

private theorem weighted_prime (eta : ℝ → ℝ) (x alpha : ℝ) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * weighted eta x alpha n) =
      smoothedExpSum eta 1 x alpha := by
  unfold smoothedExpSum weighted
  apply tsum_congr
  intro n
  rw [if_pos (Nat.coprime_one_right n)]
  ring

private theorem weighted_main (eta : ℝ → ℝ) (x alpha : ℝ) (hx : 0 < x) :
    (∫ u : ℝ, weighted eta x alpha u) =
      (x : ℂ) * (∫ t : ℝ, (eta t : ℂ) * expCircle (alpha * x * t)) := by
  have hscale := MeasureTheory.Measure.integral_comp_mul_left (weighted eta x alpha) x
  simp only [abs_of_pos (inv_pos.mpr hx), Complex.real_smul, Complex.ofReal_inv] at hscale
  have hcomp : (fun t : ℝ => weighted eta x alpha (x * t)) =
      fun t : ℝ => (eta t : ℂ) * expCircle (alpha * x * t) := by
    funext t
    unfold weighted
    rw [mul_div_cancel_left₀ t hx.ne']
    congr 1
    congr 1
    ring
  rw [hcomp] at hscale
  rw [hscale]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

theorem assemble (η : ℝ → ℝ) (c c' x α : ℝ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hnonneg : ∀ y, 0 ≤ η y)
    (hsupp : ∀ y, η y ≠ 0 → y ∈ Set.Icc c c')
    (hc : 0 < c) (hcx : (10 : ℝ) ^ 3 ≤ c * x)
    (hα : |α| ≤ 3.29 * 10 ^ 9 / (4 * Real.pi * c' * x)) :
    ‖smoothedExpSum η 1 x α - (x : ℂ) * ∫ y : ℝ, (η y : ℂ) * expCircle (α * x * y)‖ ≤
      (60 * (∫ y, |η y|) + 32 * c' * (∫ y, |deriv η y|)
          + 4 * c' ^ 2 * (∫ y, |deriv (deriv η) y|))
        * (Real.log (3.29 * 10 ^ 9) / (3 * (3.29 * 10 ^ 9))) * x
      + 2.01 / Real.sqrt c * Real.sqrt x
          * (∑ᶠ s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
                riemannZeta s = 0}, (analyticOrderNatAt riemannZeta s : ℝ))
          * (∫ y, |η y|) := by
  have hx : 0 < x := by nlinarith
  have hcompact := weighted_compact η c c' x α hx hsupp
  have hsm := weighted_smooth η hsmooth x α
  have hs : ∀ u, weighted η x α u ≠ 0 → 2 ≤ u := by
    intro u hu
    have hh := (weighted_support η c c' x α hx hsupp hu).1
    nlinarith
  have hformula := TaoFivePrimes.vonMangoldt_explicit_formula (weighted η x α) hsm hcompact hs
  have hi : Integrable (weighted η x α) := hsm.continuous.integrable_of_hasCompactSupport hcompact
  have hJ := correction_integrable _ hsm.continuous hcompact hs
  have hWeighted : (∫ u : ℝ, ((1 : ℂ) - 1 / (((u ^ 3 - u : ℝ) : ℂ))) * weighted η x α u) =
      (∫ u : ℝ, weighted η x α u) -
        (∫ u : ℝ, weighted η x α u / (((u ^ 3 - u : ℝ) : ℂ))) := by
    rw [← integral_sub hi hJ]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  have hsum := hformula.tsum_eq
  rw [hWeighted, weighted_main η x α hx, weighted_prime] at hsum
  have hseries : smoothedExpSum η 1 x α -
      (x : ℂ) * (∫ t : ℝ, (η t : ℂ) * expCircle (α * x * t)) =
      -((∑' rho : {s : ℂ // ConnesRZ.IsCriticalZero s},
        (analyticOrderNatAt riemannZeta rho.val : ℂ) *
          (∫ u : ℝ, (η (u / x) : ℂ) * expCircle (α * u) * (u : ℂ) ^ (rho.val - 1))) +
      (∫ u : ℝ, (η (u / x) : ℂ) * expCircle (α * u) / (((u ^ 3 - u : ℝ) : ℂ)))) := by
    change _ = -((∑' rho : {s : ℂ // ConnesRZ.IsCriticalZero s},
      (analyticOrderNatAt riemannZeta rho.val : ℂ) *
        (∫ u : ℝ, weighted η x α u * (u : ℂ) ^ (rho.val - 1))) +
        (∫ u : ℝ, weighted η x α u / (((u ^ 3 - u : ℝ) : ℂ))))
    linear_combination hsum
  rw [hseries, norm_neg]
  exact TaoFivePrimes.prop72_zero_series_remainder_bound η c c' x α hsmooth hnonneg hsupp hc hcx
    TaoFivePrimes.riemann_verified.1 hα

end TaoFivePrimes.Prop71Bridge

open TaoFivePrimes

theorem solution (η : ℝ → ℝ) (c c' x α : ℝ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hnonneg : ∀ y, 0 ≤ η y)
    (hsupp : ∀ y, η y ≠ 0 → y ∈ Set.Icc c c')
    (hc : 0 < c)
    (hcx : (10 : ℝ) ^ 3 ≤ c * x)
    (hα : |α| ≤ 3.29 * 10 ^ 9 / (4 * Real.pi * c' * x)) :
    ‖smoothedExpSum η 1 x α - (x : ℂ) * ∫ y : ℝ, (η y : ℂ) * expCircle (α * x * y)‖ ≤
      (60 * (∫ y, |η y|) + 32 * c' * (∫ y, |deriv η y|)
          + 4 * c' ^ 2 * (∫ y, |deriv (deriv η) y|))
        * (Real.log (3.29 * 10 ^ 9) / (3 * (3.29 * 10 ^ 9))) * x
      + 2.01 / Real.sqrt c * Real.sqrt x
          * (∑ᶠ s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
                riemannZeta s = 0}, (analyticOrderNatAt riemannZeta s : ℝ))
          * (∫ y, |η y|) := by
  exact TaoFivePrimes.Prop71Bridge.assemble η c c' x α hsmooth hnonneg hsupp hc hcx hα

end
