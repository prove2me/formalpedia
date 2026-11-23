-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.comm_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:30.208814+00:00
-- url     : https://prove2.me/submissions/9ac85b83-51a8-475d-8fe1-5bfd69559b00

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (u : V n) :
    HasFDerivAt (fun y' => fderiv ℝ g y' u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ g) y)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) y := h1.differentiableAt one_ne_zero
  exact (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp y hd.hasFDerivAt
end ReciprocityTheory.L2DbarEstimates
