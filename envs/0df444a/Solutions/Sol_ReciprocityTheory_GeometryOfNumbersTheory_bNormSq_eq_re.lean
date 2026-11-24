-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.bNormSq_eq_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:03.565918+00:00
-- url     : https://prove2.me/submissions/cc76cde4-5839-479e-aa9a-c37d4ae82af5

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_bNormSq_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
private theorem dotProduct_eq_sum_mul {r : ℕ} (u v : Fin r → ℂ) : u ⬝ᵥ v = ∑ i, u i * v i := rfl
private theorem mulVec_apply_eq_sum_pluriharmonic_analysis {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (i : Fin r) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) :
    bNormSq μ s w c = (star c ⬝ᵥ bGram μ s w *ᵥ c).re := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  have h2 : star c ⬝ᵥ bGram μ s w *ᵥ c =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * bGram μ s w i j := by
    simp only [dotProduct_eq_sum_mul, mulVec_apply_eq_sum_pluriharmonic_analysis, Pi.star_apply, Finset.mul_sum, starRingEnd_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h2, ← bNormSq_eq μ s w hI c, Complex.ofReal_re]
end ReciprocityTheory.GeometryOfNumbersTheory
