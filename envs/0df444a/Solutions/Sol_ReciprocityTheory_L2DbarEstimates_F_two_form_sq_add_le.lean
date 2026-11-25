-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.two_form_sq_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:25.307269+00:00
-- url     : https://prove2.me/submissions/c3e21ff1-9fab-4cf6-b583-34f4c90370dc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_sq_add_le

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
theorem _root_.solution (n : ℕ) (a b : Fin n → Fin n → ℂ) :
    sq2 n (fun j k => a j k + b j k) ≤ 2 * sq2 n a + 2 * sq2 n b := by
  simp only [sq2]
  have h : ∑ j, ∑ k, ‖a j k + b j k‖ ^ 2 ≤
      ∑ j, ∑ k, (2 * ‖a j k‖ ^ 2 + 2 * ‖b j k‖ ^ 2) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => cut_sq_add_le _ _
  have e : ∑ j, ∑ k, (2 * ‖a j k‖ ^ 2 + 2 * ‖b j k‖ ^ 2) =
      2 * ∑ j, ∑ k, ‖a j k‖ ^ 2 + 2 * ∑ j, ∑ k, ‖b j k‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith
end ReciprocityTheory.L2DbarEstimates.F
