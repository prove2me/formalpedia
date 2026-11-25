-- Prove2me | solution 1 for PI.FockOneDegW.Inner.fockInner_self_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:39.952946+00:00
-- url     : https://prove2.me/submissions/534ae0ad-56ba-48f6-a151-e29d4c3d22d8

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
theorem _root_.solution (F : MvPolynomial σ ℂ) : 0 ≤ (fockInner F F).re := by
  rw [fockInner_self_eq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun α _ ↦ mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)
end PI.FockOneDegW.Inner
