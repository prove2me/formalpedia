-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmRho_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:58.391879+00:00
-- url     : https://prove2.me/submissions/358a417d-332b-43b5-bf59-1afca082eadd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_hasDerivAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_deriv
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_rmRho__contDiff_ef760d6bef71

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution : ContDiff ℝ ∞ rmRho := by
  rw [contDiff_infty_iff_deriv, rmRho_deriv]
  exact ⟨fun t => (rmRho_hasDerivAt t).differentiableAt, rmRho'_contDiff⟩
end ReciprocityTheory.L2DbarEstimates.Y
