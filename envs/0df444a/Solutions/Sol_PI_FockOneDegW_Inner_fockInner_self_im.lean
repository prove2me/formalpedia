-- Prove2me | solution 1 for PI.FockOneDegW.Inner.fockInner_self_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:13.796405+00:00
-- url     : https://prove2.me/submissions/c9ee69f4-0c57-4f73-aa72-e47093d2c1f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action FockRaiseLowInner
open PI PI.FockOneDegW PI.FockOneDegW.Inner
variable {σ : Type*}
namespace PI.FockOneDegW.Inner
theorem _root_.solution (F : MvPolynomial σ ℂ) : (fockInner F F).im = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_im]
end PI.FockOneDegW.Inner
