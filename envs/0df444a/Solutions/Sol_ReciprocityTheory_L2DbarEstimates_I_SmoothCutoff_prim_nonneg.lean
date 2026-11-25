-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:54.791953+00:00
-- url     : https://prove2.me/submissions/5c893eeb-5380-470c-a198-6eb4ebc05939

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_monotone
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_of_le_half

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
theorem _root_.solution (t : ℝ) : 0 ≤ prim t := by
  have := prim_monotone (min_le_left t (1 / 2))
  rwa [prim_of_le_half (min_le_right t (1 / 2))] at this
end ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
