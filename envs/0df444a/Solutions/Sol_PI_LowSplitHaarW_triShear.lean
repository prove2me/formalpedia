-- Prove2me | solution 1 for PI.LowSplitHaarW.triShear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:29.699856+00:00
-- url     : https://prove2.me/submissions/8466228d-d6cf-41d2-b8cc-1d5b8e40725c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_MeasurePreservingOfCard
import Theorems.Thm_PI_LowSplitHaarW_measurePreserving_of_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.LowSplitHaarW
namespace PI.LowSplitHaarW
theorem _root_.solution : TriShear := by
  intro ι _ _ r g hg hdep
  exact measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep
end PI.LowSplitHaarW
