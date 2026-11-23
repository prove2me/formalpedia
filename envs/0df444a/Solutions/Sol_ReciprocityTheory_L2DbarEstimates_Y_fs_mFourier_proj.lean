-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fs_mFourier_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:37.541101+00:00
-- url     : https://prove2.me/submissions/3de6597d-d93d-4982-948e-559bccd4854e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum

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
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : ℕ} (m : Fin f → ℤ) (t : Fin f → ℝ) :
    UnitAddTorus.mFourier m (fsProj f t) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ k, (m k : ℂ) * (t k : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fsProj, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring
end ReciprocityTheory.L2DbarEstimates.Y
