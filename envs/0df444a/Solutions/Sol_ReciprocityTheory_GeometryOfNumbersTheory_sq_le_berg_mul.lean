-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sq_le_berg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:36.329438+00:00
-- url     : https://prove2.me/submissions/e9ee5558-8f3a-41ad-9712-5b53ebc95aa9

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_posDef_norm_dot_sq_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_bNormSq_eq_re
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_berg_eq_quad
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sum_mul_eq_star_dot

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
    (hw : ∀ x, 0 ≤ w x)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (hpos : (bGram μ s w).PosDef) (c : Fin r → ℂ) (x : X) :
    ‖∑ i, c i * s i x‖ ^ 2 * w x ≤ bergmanDensity μ s w x * bNormSq μ s w c := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  rw [sum_mul_eq_star_dot, berg_eq_quad, bNormSq_eq_re μ s w hI c]
  have h := mul_le_mul_of_nonneg_right (posDef_norm_dot_sq_le hpos c (star fun i => s i x)) (hw x)
  refine le_trans h (le_of_eq ?_)
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
