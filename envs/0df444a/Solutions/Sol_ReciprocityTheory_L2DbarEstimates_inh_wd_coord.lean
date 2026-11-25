-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.inh_wd_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:52.246796+00:00
-- url     : https://prove2.me/submissions/f3da5a0a-6fe3-437d-af0e-e4868cca34c0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_InhHasFDerivAtNormSq

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
theorem _root_.solution (n : ℕ) (j k : Fin n) (y : V n) :
    wd n j (fun y : V n => y k) y = if j = k then 1 else 0 := by
  have h : (fun y : V n => y k) = ⇑((EuclideanSpace.proj k : V n →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext y; simp
  unfold wd
  rw [h, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', bas]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]
end ReciprocityTheory.L2DbarEstimates
