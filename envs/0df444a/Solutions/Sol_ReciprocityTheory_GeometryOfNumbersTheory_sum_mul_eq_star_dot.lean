-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sum_mul_eq_star_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:58.519826+00:00
-- url     : https://prove2.me/submissions/86df353c-f0fa-4059-a90a-92f60d67747f

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
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} (s : Fin r → X → ℂ) (c : Fin r → ℂ) (x : X) :
    ∑ i, c i * s i x = star (star fun i => s i x) ⬝ᵥ c := by
  rw [star_star, dotProduct_eq_sum_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end ReciprocityTheory.GeometryOfNumbersTheory
