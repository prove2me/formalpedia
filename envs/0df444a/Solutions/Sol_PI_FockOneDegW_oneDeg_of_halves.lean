-- Prove2me | solution 1 for PI.FockOneDegW.oneDeg_of_halves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:04.106371+00:00
-- url     : https://prove2.me/submissions/3ad05848-5175-4a12-a60b-181090458792

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution (h1 : FirstHalf) (h2 : SecondHalf) : PI.FockDegreeTwoParts.OneDeg :=
  fun p q r s => ⟨h1 p q r s, h2 p q r s⟩
end PI.FockOneDegW
