-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_gradient_coordinate_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:10:36.287874+00:00
-- url     : https://prove2.me/submissions/75ce64a1-ce5f-4404-a7ee-396c543112ff

import Theorems.Thm_ZeroFreeRRG_Hardcore_centered_product_coordinate_cancellation
import Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_product_coordinate
import Mathlib
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : ℝ)
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : (∫ x : ℝ, x ∂μ) = 0)
    (φ : ℝ → ℝ) (hφ : Integrable φ μ) (hxφ : Integrable (fun x => x*φ x) μ)
    (i : Fin d)
    (hN : ∀ j, Integrable (fun xs : Fin d → ℝ =>
      ((∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) * φ (xs i))
      (Measure.pi fun _ : Fin d => μ))
    (hP : Integrable (fun xs : Fin d → ℝ => (∏ k, (1+θ*xs k)) * φ (xs i))
      (Measure.pi fun _ : Fin d => μ))
    (hQ : Integrable (fun xs : Fin d → ℝ => (∏ k, (1-xs k)) * φ (xs i))
      (Measure.pi fun _ : Fin d => μ)) :
    (∫ xs : Fin d → ℝ, ((1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k))*φ (xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = 0 := by
  let ν := Measure.pi fun _ : Fin d => μ
  let N := fun (j : Fin d) (xs : Fin d → ℝ) =>
    ((∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) * φ (xs i)
  let P := fun xs : Fin d → ℝ => (∏ k, (1+θ*xs k)) * φ (xs i)
  let Q := fun xs : Fin d → ℝ => (∏ k, (1-xs k)) * φ (xs i)
  have hA : (∫ x : ℝ, (1+θ*x) ∂μ) = 1 := by
    rw [integral_add (integrable_const 1) (hint.const_mul θ),integral_const_mul]
    simp [hmean]
  have hB : (∫ x : ℝ, (1-x) ∂μ) = 1 := by
    rw [integral_sub (integrable_const 1) hint]
    simp [hmean]
  have hPi : (∫ xs, P xs ∂ν) = (∫ x, φ x ∂μ) + θ*(∫ x, x*φ x ∂μ) := by
    rw [normalized_product_coordinate d μ (fun x => 1+θ*x) φ hA i]
    have hh : (fun x : ℝ => (1+θ*x)*φ x) = fun x => φ x + θ*(x*φ x) := by funext x; ring
    rw [hh,integral_add hφ (hxφ.const_mul θ),integral_const_mul]
  have hQi : (∫ xs, Q xs ∂ν) = (∫ x, φ x ∂μ) - (∫ x, x*φ x ∂μ) := by
    rw [normalized_product_coordinate d μ (fun x => 1-x) φ hB i]
    have hh : (fun x : ℝ => (1-x)*φ x) = fun x => φ x - x*φ x := by funext x; ring
    rw [hh,integral_sub hφ hxφ]
  have hNi (j : Fin d) : (∫ xs, N j xs ∂ν) = if i=j then (∫ x, x*φ x ∂μ) else 0 :=
    centered_product_coordinate_cancellation d μ θ hint hmean φ i j
  have hsum : (∫ xs, ∑ j, N j xs ∂ν) = (∫ x, x*φ x ∂μ) := by
    rw [integral_finsetSum Finset.univ (fun j hj => hN j)]
    change (∑ j, ∫ xs, N j xs ∂ν) = (∫ x, x*φ x ∂μ)
    simp [hNi, eq_comm]
  have hS : Integrable (fun xs => ∑ j, N j xs) ν := by
    apply integrable_finsetSum
    exact fun j _ => hN j
  have hc : Integrable (fun xs => (1+θ)*(∑ j, N j xs)) ν := hS.const_mul _
  have hall : Integrable (fun xs => (1+θ)*(∑ j, N j xs)+Q xs) ν := hc.add hQ
  have heq : (fun xs : Fin d → ℝ => ((1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k))*φ (xs i)) =
      fun xs => (1+θ)*(∑ j, N j xs)+Q xs-P xs := by
    funext xs
    dsimp [N,P,Q]
    rw [← Finset.sum_mul]
    ring
  rw [heq]
  have hsub := integral_sub hall hP
  rw [hsub,integral_add hc hQ,integral_const_mul,hsum,hPi,hQi]
  ring
