-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.normSq_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:08.692424+00:00
-- url     : https://prove2.me/submissions/1e47cc93-34ca-4c26-ad7f-8cc24be7076b

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt

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
theorem _root_.solution {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (c : Fin r → ℂ) (x : X) :
    ‖∑ i, c i * s i x‖ ^ 2 * w x =
      (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))).re := by
  have h : ((‖∑ i, c i * s i x‖ ^ 2 * w x : ℝ) : ℂ) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) := by
    push_cast
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]; ring
  rw [← h, Complex.ofReal_re]
end ReciprocityTheory.GeometryOfNumbersTheory
