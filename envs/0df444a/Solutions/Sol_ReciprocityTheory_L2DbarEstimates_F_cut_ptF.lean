-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_ptF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:58.183085+00:00
-- url     : https://prove2.me/submissions/7e83e2d9-e804-4afd-b151-71af0baa2f15

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
private lemma norm_ofReal_sq_le_one_of_abs_le_one (c : ℝ) (hc : |c| ≤ 1) : ‖(c : ℂ)‖ ^ 2 ≤ 1 := by
  have h1 : ‖(c : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hc
  nlinarith [norm_nonneg (c : ℂ)]
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} (c : ℝ) (hc : |c| ≤ 1) (v : V n) : ‖(c : ℂ) • v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow]
  have h2 := norm_ofReal_sq_le_one_of_abs_le_one c hc
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (sq_nonneg ‖v‖)]
end ReciprocityTheory.L2DbarEstimates.F
