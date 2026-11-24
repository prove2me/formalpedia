-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.berg_eq_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:57.583338+00:00
-- url     : https://prove2.me/submissions/9ad71b5a-9c4a-4b1c-a0d9-1c74ee2b7c0a

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
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
theorem _root_.solution (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (x : X) :
    bergmanDensity μ s w x = w x * (star (star fun i => s i x) ⬝ᵥ (bGram μ s w)⁻¹ *ᵥ star fun i => s i x).re := by
  unfold bergmanDensity
  rw [star_star]
  congr 2
  simp only [dotProduct_eq_sum_mul, mulVec_apply_eq_sum_pluriharmonic_analysis, Pi.star_apply, Finset.mul_sum, starRingEnd_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.GeometryOfNumbersTheory
