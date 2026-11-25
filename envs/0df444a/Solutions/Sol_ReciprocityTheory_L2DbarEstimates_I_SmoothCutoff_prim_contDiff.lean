-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:16:56.115871+00:00
-- url     : https://prove2.me/submissions/b7cc8de7-87df-4856-b3d8-92f8bfbab662

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_bump_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_hasDerivAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_deriv_prim

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
theorem _root_.solution : ContDiff ℝ ∞ prim :=
  contDiff_infty_iff_deriv.2
    ⟨fun t => (prim_hasDerivAt t).differentiableAt, by rw [deriv_prim]; exact bump_contDiff⟩
end ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
