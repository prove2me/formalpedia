-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.finite_product_density
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:52:57.975261+00:00
-- url     : https://prove2.me/submissions/80f769bc-dffe-4054-9eae-f5ba1af3db48

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

theorem solution {ι : Type} [Fintype ι] (μ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (f : ι → ℝ → ℝ)
    (hpos : ∀ i x, 0 ≤ f i x) (hint : ∀ i, Integrable (f i) (μ i)) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun xs => ENNReal.ofReal (∏ i, f i (xs i))) := by
  letI : ∀ i, IsFiniteMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (f i x))) :=
    fun i => isFiniteMeasure_withDensity_ofReal (hint i).hasFiniteIntegral
  apply Measure.pi_eq
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  rw [Measure.restrict_pi_pi]
  have hi : Integrable (fun xs : ι → ℝ => ∏ i, f i (xs i))
      (Measure.pi (fun i => (μ i).restrict (S i))) :=
    Integrable.fintype_prod (fun i => (hint i).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun xs => Finset.prod_nonneg (fun i _ => hpos i (xs i))))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i hi'
    rw [withDensity_apply _ (hS i)]
    exact ofReal_integral_eq_lintegral_ofReal (hint i).restrict
      (Filter.Eventually.of_forall (hpos i))
  · intro i hi'
    exact integral_nonneg (fun x => hpos i x)
