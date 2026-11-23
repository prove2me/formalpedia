-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:36.691079+00:00
-- url     : https://prove2.me/submissions/8e9cc7ca-931f-4a9e-8ce9-0faa69b490f2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (w : V n) : w = ∑ j, w j • bas n j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w]
  simp [bas]
end ReciprocityTheory.L2DbarEstimates.Y
