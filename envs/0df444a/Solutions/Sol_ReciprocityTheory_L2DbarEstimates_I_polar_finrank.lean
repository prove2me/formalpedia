-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.polar_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:13.143078+00:00
-- url     : https://prove2.me/submissions/b9367e36-bfa2-41a1-b7f7-6f89c33c2b2c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_PolarBallReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) : finrank ℝ (V n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
end ReciprocityTheory.L2DbarEstimates.I
