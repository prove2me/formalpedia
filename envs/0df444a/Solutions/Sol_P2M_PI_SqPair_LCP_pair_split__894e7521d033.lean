-- Prove2me | solution 1 for P2M_PI_SqPair_LCP_pair_split__894e7521d033
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:39:46.306301+00:00
-- url     : https://prove2.me/submissions/91c2fc59-ea05-4542-9bfd-653371231358

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpSplit
import Theorems.Thm_PI_SqPair_LCP_split_of
import Theorems.Thm_PI_SqPair_LCP_split_off_hyperbolic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.SqPair PI.SqPair.LCP
namespace PI.SqPair.LCP
theorem _root_.solution : Split := split_of split_off_hyperbolic
end PI.SqPair.LCP
