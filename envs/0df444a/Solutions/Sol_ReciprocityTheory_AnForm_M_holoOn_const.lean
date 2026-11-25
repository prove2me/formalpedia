-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holoOn_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:58.391472+00:00
-- url     : https://prove2.me/submissions/68de85a6-226e-4982-a01d-312860686fe4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (U : Set (OnePoint ℂ)) (c : ℂ) : p1.HoloOn U (fun _ => c) := by
  intro j w _
  exact analyticAt_const
end ReciprocityTheory.AnForm.M
