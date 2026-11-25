-- Prove2me | solution 1 for PI.ZW.rightOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:33.184697+00:00
-- url     : https://prove2.me/submissions/8350f356-518c-484c-b547-068a236e6f03

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Jensen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Assemble
import Theorems.Thm_PI_ZW_jensenCount
import Theorems.Thm_PI_ZW_rightOne_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution : RightOne := rightOne_of jensenCount
end PI.ZW
