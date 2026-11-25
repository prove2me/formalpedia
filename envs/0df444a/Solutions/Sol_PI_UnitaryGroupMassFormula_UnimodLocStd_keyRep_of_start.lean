-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.keyRep_of_start
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:22:32.228008+00:00
-- url     : https://prove2.me/submissions/5e23bb23-5006-48f7-b442-59e5e989d0ee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyNewton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepKey
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_keyExact
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_keyNewton
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_keyRep_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hS : KeyStart) : KeyRep := keyRep_of hS keyNewton keyExact
end PI.UnitaryGroupMassFormula.UnimodLocStd
