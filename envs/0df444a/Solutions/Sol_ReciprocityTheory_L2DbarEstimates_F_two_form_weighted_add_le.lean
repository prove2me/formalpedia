-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.two_form_weighted_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:55.883201+00:00
-- url     : https://prove2.me/submissions/d31d2249-a817-455c-b7ef-5d9f5795627a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (a b : Fin n → Fin n → ℂ) (X : ℝ) (hX : 0 ≤ X) :
    ENNReal.ofReal (sq2 n (a + b) * X) ≤
      2 * ENNReal.ofReal (sq2 n a * X) + 2 * ENNReal.ofReal (sq2 n b * X) := by
  have hpt : ∀ j k, ‖(a + b) j k‖ ^ 2 ≤ 2 * ‖a j k‖ ^ 2 + 2 * ‖b j k‖ ^ 2 := fun j k => by
    have := norm_add_le (a j k) (b j k)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖a j k‖ - ‖b j k‖), norm_nonneg (a j k + b j k), norm_nonneg (a j k),
      norm_nonneg (b j k)]
  have h1 : sq2 n (a + b) ≤ 2 * sq2 n a + 2 * sq2 n b := by
    unfold sq2
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpt j k
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith
  have hsa : 0 ≤ sq2 n a := by
    unfold sq2
    positivity
  have hsb : 0 ≤ sq2 n b := by
    unfold sq2
    positivity
  calc ENNReal.ofReal (sq2 n (a + b) * X) ≤ ENNReal.ofReal (2 * (sq2 n a * X) + 2 * (sq2 n b * X)) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = 2 * ENNReal.ofReal (sq2 n a * X) + 2 * ENNReal.ofReal (sq2 n b * X) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg hsa hX))
            (mul_nonneg (by norm_num) (mul_nonneg hsb hX)), ENNReal.ofReal_mul (p := 2) (by norm_num),
          ENNReal.ofReal_mul (p := 2) (by norm_num)]
        simp
end ReciprocityTheory.L2DbarEstimates.F
