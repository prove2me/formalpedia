-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_rmRho__monotone_29154a1d1bb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:14:31.183606+00:00
-- url     : https://prove2.me/submissions/978d9823-4b41-4a06-9612-c62f53a22cfc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmStep_monotone

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
theorem _root_.solution : Monotone rmRho' := by
  intro a b h
  have h1 := rmStep_monotone h
  have h2 := rmStep_monotone (show -b ≤ -a by linarith)
  unfold rmRho'
  linarith
end ReciprocityTheory.L2DbarEstimates.Y
