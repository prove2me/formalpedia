-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.IsHalfReps.card_xsOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:22.766855+00:00
-- url     : https://prove2.me/submissions/6accf39f-a111-4131-91ab-00457e5d1c51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsHalfReps_injOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}
namespace ReciprocityTheory.ChartRestriction.L1
namespace IsHalfReps
theorem _root_.solution (h : IsHalfReps L α T) : (xsOf L T).card = T.card :=
  Finset.card_image_of_injOn h.injOn
end IsHalfReps
end ReciprocityTheory.ChartRestriction.L1
