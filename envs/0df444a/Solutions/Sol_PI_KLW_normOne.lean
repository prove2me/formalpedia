-- Prove2me | solution 1 for PI.KLW.normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:28.5246+00:00
-- url     : https://prove2.me/submissions/bf92b187-5222-4c94-9306-6fceae7cd9b3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOne
import Theorems.Thm_PI_KLW_normOne_of
import Theorems.Thm_PI_KLW_pairOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.KLW
namespace PI.KLW
theorem _root_.solution : NormOne := normOne_of pairOne
end PI.KLW
