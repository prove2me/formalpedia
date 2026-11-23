-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.vec_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:28.303631+00:00
-- url     : https://prove2.me/submissions/26be6dca-da1c-4adf-a0cf-dff0f800d86a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (w : V n) : w = ∑ j, w j • bas n j := by
  have h := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr w
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  rfl
end ReciprocityTheory.L2DbarEstimates.Y
