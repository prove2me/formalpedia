-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.tilted_product_expectation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:00:34.260036+00:00
-- url     : https://prove2.me/submissions/ebed5369-f91b-46b4-8448-b83d145a30c4

import Theorems.Thm_ZeroFreeRRG_Hardcore_finite_product_density
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators ENNReal

theorem solution (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f W : ℝ → ℝ) (hf : Measurable f) (hW : Measurable W)
    (hpos : ∀ x, 0 ≤ f x) (hint : Integrable f μ)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))]
    (K : (Fin d → ℝ) → ℝ) (hK : Measurable K) :
    let ν := Measure.map W (μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (∫ xs : Fin d → ℝ, K xs ∂(Measure.pi fun _ : Fin d => ν)) =
    ∫ xs : Fin d → ℝ, (∏ i, f (xs i)) * K (fun i => W (xs i))
      ∂(Measure.pi fun _ : Fin d => μ) := by
  dsimp only
  let τ := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let ν := Measure.map W τ
  let P := fun xs : Fin d → ℝ => fun i => W (xs i)
  let ρ := fun xs : Fin d → ℝ => ∏ i, f (xs i)
  have hP : Measurable P := by
    apply measurable_pi_lambda
    intro i
    exact hW.comp (measurable_pi_apply i)
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
  have hρ0 (xs : Fin d → ℝ) : 0 ≤ ρ xs := Finset.prod_nonneg (fun i _ => hpos (xs i))
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hmap : Measure.map P (Measure.pi fun _ : Fin d => τ) = Measure.pi (fun _ : Fin d => ν) := by
    exact Measure.pi_map_pi (fun _ => hW.aemeasurable)
  have htilt : (Measure.pi fun _ : Fin d => τ) =
      (Measure.pi fun _ : Fin d => μ).withDensity (fun xs => ENNReal.ofReal (ρ xs)) := by
    exact finite_product_density (fun _ : Fin d => μ) (fun _ => f) (fun _ => hpos) (fun _ => hint)
  change (∫ xs, K xs ∂(Measure.pi fun _ : Fin d => ν)) =
    ∫ xs, ρ xs * K (P xs) ∂(Measure.pi fun _ : Fin d => μ)
  rw [← hmap, integral_map hP.aemeasurable hK.aestronglyMeasurable, htilt]
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xs => by simp only [ENNReal.toReal_ofReal (hρ0 xs), smul_eq_mul])
