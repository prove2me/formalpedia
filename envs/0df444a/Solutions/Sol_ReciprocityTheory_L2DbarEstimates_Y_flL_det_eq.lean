-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:51.737339+00:00
-- url     : https://prove2.me/submissions/f5fe1315-037b-4fa0-bbb8-cddeb536695f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (f : V n →L[ℂ] V n) :
    f.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∏ c, f (bas n c) (σ c) := by

  simp only [ContinuousLinearMap.det]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [LinearMap.toMatrix_apply, bas, Units.smul_def, zsmul_eq_mul]
end ReciprocityTheory.L2DbarEstimates.Y
