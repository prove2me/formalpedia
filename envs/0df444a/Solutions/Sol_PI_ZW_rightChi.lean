-- Prove2me | solution 1 for PI.ZW.rightChi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:43:57.331369+00:00
-- url     : https://prove2.me/submissions/226412a5-3bf1-4e20-ae5a-3e6af7a41cf5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Jensen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Assemble
import Theorems.Thm_PI_ZW_jensenCount
import Theorems.Thm_PI_ZW_rightChi_of


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
theorem _root_.solution : RightChi := rightChi_of jensenCount
end PI.ZW
