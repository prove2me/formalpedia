-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:55.153238+00:00
-- url     : https://prove2.me/submissions/7c646466-482f-4919-ac06-bf4948c96b3e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_monotone
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_of_one_le

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
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
open ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
namespace ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
theorem _root_.solution (t : ℝ) : prim t ≤ prim 1 := by
  have := prim_monotone (le_max_left t 1)
  rwa [prim_of_one_le (le_max_right t 1)] at this
end ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
