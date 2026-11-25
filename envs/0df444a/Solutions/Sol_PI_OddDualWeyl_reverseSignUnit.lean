-- Prove2me | solution 1 for PI.OddDualWeyl.reverseSignUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:38.297625+00:00
-- url     : https://prove2.me/submissions/7b816017-119a-4422-b4b0-c661e1b87fc5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe
import Theorems.Thm_PI_OddDualWeyl_Misc_sgn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
namespace PI.OddDualWeyl
theorem _root_.solution : SgnPM := by
  intro K _ m
  exact PI.OddDualWeyl.Misc.sgn K m
end PI.OddDualWeyl
