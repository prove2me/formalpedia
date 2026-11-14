-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_gradient_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:12:21.010916+00:00
-- url     : https://prove2.me/submissions/44f635d1-39a8-4b6d-916f-321bcf8c5878

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_coordinate_cancellation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 0 < d) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : ℝ)
    (hb : ∀ᵐ x ∂μ, -1 ≤ x ∧ x ≤ 1)
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ xs : Fin d → ℝ, ((1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k)) ∂(Measure.pi fun _ : Fin d => μ)) = 0 := by
  let ν := Measure.pi fun _ : Fin d => μ
  let cube : Set (Fin d → ℝ) := Set.pi univ (fun _ => Icc (-1:ℝ) 1)
  have hcube : IsCompact cube := isCompact_univ_pi fun _ : Fin d => isCompact_Icc
  have hgood : ∀ᵐ xs ∂ν, xs ∈ cube := by
    have hh : ∀ᵐ xs ∂ν, ∀ i, -1 ≤ xs i ∧ xs i ≤ 1 := by
      apply Measure.ae_pi_le_pi
      exact Filter.eventually_pi (fun _ : Fin d => hb)
    filter_upwards [hh] with xs hx
    exact fun i hi => hx i
  have hci (F : (Fin d → ℝ) → ℝ) (hF : Continuous F) : Integrable F ν := by
    obtain ⟨B,hB⟩ := hcube.exists_bound_of_continuousOn hF.continuousOn
    apply Integrable.of_bound hF.measurable.aestronglyMeasurable B
    filter_upwards [hgood] with xs hx
    exact hB xs hx
  let i : Fin d := ⟨0,hd⟩
  have hN (j : Fin d) : Integrable (fun xs : Fin d → ℝ =>
      ((∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) * (1:ℝ)) ν := by
    apply hci
    fun_prop
  have hP : Integrable (fun xs : Fin d → ℝ => (∏ k, (1+θ*xs k))*(1:ℝ)) ν := by
    apply hci
    fun_prop
  have hQ : Integrable (fun xs : Fin d → ℝ => (∏ k, (1-xs k))*(1:ℝ)) ν := by
    apply hci
    fun_prop
  have h := hardcore_gradient_coordinate_cancellation d μ θ hint hmean (fun _ => (1:ℝ))
    (integrable_const 1) (by simpa using hint) i hN hP hQ
  simpa using h
