-- Prove2me | solution 1 for PI.AddIntG.Wk.addIntG_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:28.896379+00:00
-- url     : https://prove2.me/submissions/225c80f2-d0b0-4d52-b4ef-050b68562d48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_AddIntGTop
import Theorems.Thm_PI_AddIntG_Wk_formalGroupLawExists
import Theorems.Thm_PI_AddIntG_Wk_glue_holds_var


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AddIntG PI.AddIntG.Wk
namespace PI.AddIntG.Wk
theorem _root_.solution : PI.AddIntG.Target := glue_holds_var formalGroupLawExists
end PI.AddIntG.Wk
