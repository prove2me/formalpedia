-- Prove2me | solution 2 for P2M_PI_DIP_NormOne_coe___e90390e50a53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:43.643957+00:00
-- url     : https://prove2.me/submissions/e379e3c5-9157-4e21-b652-d1bd54a86eb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open PI PI.DIP PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace PI.DIP.NormOne
theorem _root_.solution (c : E →+* E) (y : 𝓞 E) : ((σ c y : 𝓞 E) : E) = c (y : E) := rfl
end PI.DIP.NormOne
