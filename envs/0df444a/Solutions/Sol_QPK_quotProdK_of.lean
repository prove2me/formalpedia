-- Prove2me | solution 1 for QPK.quotProdK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:32.622803+00:00
-- url     : https://prove2.me/submissions/6d99ee3f-27a3-49cc-8b72-902c2480d43f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_QuotProdKOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open QPK
namespace QPK
theorem _root_.solution (hA : GlobAsm) (hU : HaarUniq) (hL : LocPack) : PI.QuotProdK.QuotProdK :=
  hA hU hL
end QPK
