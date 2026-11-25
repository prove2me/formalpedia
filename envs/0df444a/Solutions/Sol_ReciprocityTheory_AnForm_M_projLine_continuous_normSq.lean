-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_continuous_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:51.797139+00:00
-- url     : https://prove2.me/submissions/46a7993b-80dc-419d-818b-03f71a7fa2c3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst

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
theorem _root_.solution : Continuous (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) := (continuous_norm.comp (continuous_apply 0)).pow 2
end ReciprocityTheory.AnForm.M
