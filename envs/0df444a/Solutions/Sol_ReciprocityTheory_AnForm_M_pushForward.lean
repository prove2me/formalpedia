-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushForward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:38.125285+00:00
-- url     : https://prove2.me/submissions/1cbd1759-7448-4138-944c-a743146b562a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushBForward
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushLocalStatement
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushB_forward


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : PushForwardStatement := pushB_forward
end ReciprocityTheory.AnForm.M
