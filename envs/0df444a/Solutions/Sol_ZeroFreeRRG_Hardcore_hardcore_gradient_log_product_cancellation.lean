-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_gradient_log_product_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:10:36.352252+00:00
-- url     : https://prove2.me/submissions/29b6ec61-b3e8-4f4c-b969-44a74eae4d92

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_coordinate_cancellation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ x ∂μ, -1 ≤ x ∧ x ≤ 1)
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ xs : Fin d → ℝ, ((1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k)) * ∑ i, Real.log (1+θ*xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = 0 := by
  let ν := Measure.pi fun _ : Fin d => μ
  let cube : Set (Fin d → ℝ) := Set.pi univ (fun _ => Icc (-1:ℝ) 1)
  let φ := fun x : ℝ => Real.log (1+θ*x)
  let U := fun xs : Fin d → ℝ => (1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k)
  have hpos (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : 0 < 1+θ*x := by
    nlinarith [mul_nonneg hθ (show 1+x ≥ 0 by linarith)]
  have hcube : IsCompact cube := isCompact_univ_pi fun _ : Fin d => isCompact_Icc
  have hgood : ∀ᵐ xs ∂ν, xs ∈ cube := by
    have hh : ∀ᵐ xs ∂ν, ∀ i, -1 ≤ xs i ∧ xs i ≤ 1 := by
      apply Measure.ae_pi_le_pi
      exact Filter.eventually_pi (fun _ : Fin d => hb)
    filter_upwards [hh] with xs hx
    exact fun i hi => hx i
  have hci (F : (Fin d → ℝ) → ℝ) (hm : Measurable F) (hc : ContinuousOn F cube) : Integrable F ν := by
    obtain ⟨B,hB⟩ := hcube.exists_bound_of_continuousOn hc
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [hgood] with xs hx
    exact hB xs hx
  have hci1 (F : ℝ → ℝ) (hm : Measurable F) (hc : ContinuousOn F (Icc (-1:ℝ) 1)) : Integrable F μ := by
    obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).exists_bound_of_continuousOn hc
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [hb] with x hx
    exact hB x hx
  have hφm : Measurable φ := by dsimp [φ]; fun_prop
  have hφc : ContinuousOn φ (Icc (-1:ℝ) 1) := by
    dsimp [φ]
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    exact ne_of_gt (hpos x hx)
  have hφi : Integrable φ μ := hci1 φ hφm hφc
  have hxφi : Integrable (fun x => x*φ x) μ :=
    hci1 _ (measurable_id.mul hφm) (continuousOn_id.mul hφc)
  have hφcoord (i : Fin d) : ContinuousOn (fun xs : Fin d → ℝ => φ (xs i)) cube := by
    apply hφc.comp (continuous_apply i).continuousOn
    intro xs hxs
    exact hxs i (mem_univ i)
  have hN (i j : Fin d) : Integrable (fun xs : Fin d → ℝ =>
      ((∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) * φ (xs i)) ν := by
    apply hci
    · dsimp [φ]; fun_prop
    · exact (show Continuous (fun xs : Fin d → ℝ => (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) by fun_prop).continuousOn.mul (hφcoord i)
  have hP (i : Fin d) : Integrable (fun xs : Fin d → ℝ => (∏ k, (1+θ*xs k))*φ (xs i)) ν := by
    apply hci
    · dsimp [φ]; fun_prop
    · exact (show Continuous (fun xs : Fin d → ℝ => ∏ k, (1+θ*xs k)) by fun_prop).continuousOn.mul (hφcoord i)
  have hQ (i : Fin d) : Integrable (fun xs : Fin d → ℝ => (∏ k, (1-xs k))*φ (xs i)) ν := by
    apply hci
    · dsimp [φ]; fun_prop
    · exact (show Continuous (fun xs : Fin d → ℝ => ∏ k, (1-xs k)) by fun_prop).continuousOn.mul (hφcoord i)
  have hUφ (i : Fin d) : Integrable (fun xs => U xs * φ (xs i)) ν := by
    apply hci
    · dsimp [U,φ]; fun_prop
    · exact (show Continuous U by dsimp [U]; fun_prop).continuousOn.mul (hφcoord i)
  have hcanc (i : Fin d) : (∫ xs, U xs * φ (xs i) ∂ν) = 0 :=
    hardcore_gradient_coordinate_cancellation d μ θ hint hmean φ hφi hxφi i (hN i) (hP i) (hQ i)
  change (∫ xs, U xs * ∑ i, φ (xs i) ∂ν) = 0
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i hi => hUφ i)]
  change (∑ i, ∫ xs, U xs * φ (xs i) ∂ν) = 0
  simp [hcanc]
