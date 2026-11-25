-- Prove2me | solution 1 for PI.FockOneDegW.oneDeg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:53.587394+00:00
-- url     : https://prove2.me/submissions/30468219-f6a2-40c1-83dd-b6661b67cec1

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Theorems.Thm_PI_FockOneDegW_oneDeg_of_halves

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
theorem _root_.solution (hT : HwHarmDeg) (hR : Reduction) (hS : Swap) : PI.FockDegreeTwoParts.OneDeg :=
  oneDeg_of_halves (hR hT) (hS (hR hT))
end PI.FockOneDegW
