-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pshShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:37:23.622628+00:00
-- url     : https://prove2.me/submissions/3af9c116-46c2-4822-aafd-32f3aea4f2ac

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShift
import Theorems.Thm_ReciprocityTheory_AnForm_M_plurisubharmonicShift_proof


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : PshShiftStatement := plurisubharmonicShift_proof
end ReciprocityTheory.AnForm.M
