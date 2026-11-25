-- Prove2me | solution 1 for PI.OneCosetSharp.W.oneCosetSharp_of_patClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:44.956128+00:00
-- url     : https://prove2.me/submissions/d4d3369b-2a23-483c-9fb1-c0f91e625693

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_OneCosetSharpOfPatClosed
import Theorems.Thm_PI_OneCosetSharp_W_oneCosetSharp_of
import Theorems.Thm_PI_OneCosetSharp_W_claim1_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.OneCosetSharp PI.OneCosetSharp.W
namespace PI.OneCosetSharp.W
theorem _root_.solution (hP : PatClosed) (hK : KappaZero) (hN : NElem) (hG : GaStep) (h2 : Claim2) :
    OneCosetSharp :=
  oneCosetSharp_of (claim1_of hP hK hN hG) h2
end PI.OneCosetSharp.W
