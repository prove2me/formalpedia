-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.chi_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:16:03.057844+00:00
-- url     : https://prove2.me/submissions/f5aea589-2e79-4b9d-a30b-2eae434dce75

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_hasDerivAt

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
theorem _root_.solution (t : ℝ) : HasDerivAt chi (-(bump t / prim 1)) t :=
  ((prim_hasDerivAt t).div_const (prim 1)).const_sub 1
end ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
