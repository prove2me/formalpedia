-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.bNormSq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:57.424453+00:00
-- url     : https://prove2.me/submissions/a4058dd1-da9d-4266-9532-7f14b71e2a65

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) :
    (bNormSq μ s w c : ℂ) = ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * bGram μ s w i j := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  have hpt : ∀ x, ((‖∑ i, c i * s i x‖ ^ 2 * w x : ℝ) : ℂ) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) := by
    intro x
    rw [Complex.ofReal_mul, Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]
    ring
  have hJ : ∀ i ∈ (Finset.univ : Finset (Fin r)), Integrable (fun x => ∑ j, starRingEnd ℂ (c i) * c j *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    fun i _ => integrable_finset_sum _ fun j _ => (hI i j).const_mul _
  have hK : ∀ i, ∀ j ∈ (Finset.univ : Finset (Fin r)), Integrable (fun x => starRingEnd ℂ (c i) * c j *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    fun i j _ => (hI i j).const_mul _
  unfold bNormSq
  rw [← integral_complex_ofReal]
  simp only [hpt]
  rw [integral_finset_sum _ hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (hK i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl
end ReciprocityTheory.GeometryOfNumbersTheory
