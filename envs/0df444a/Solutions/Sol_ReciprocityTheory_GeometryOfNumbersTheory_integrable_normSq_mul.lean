-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integrable_normSq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:24.994007+00:00
-- url     : https://prove2.me/submissions/9fd3af1a-45f7-48ea-a4e1-c5e553900b9c

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_normSq_mul_eq

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
    (c : Fin r → ℂ) : Integrable (fun x => ‖∑ i, c i * s i x‖ ^ 2 * w x) μ := by
  have hF : Integrable (fun x => ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _
  exact hF.re.congr (Filter.Eventually.of_forall fun x => (normSq_mul_eq s w c x).symm)
end ReciprocityTheory.GeometryOfNumbersTheory
