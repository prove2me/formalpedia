-- Prove2me | solution 1 for PI.FockOneDegW.Inner.fockInner_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:57.744804+00:00
-- url     : https://prove2.me/submissions/9cba4d26-41ab-4233-9124-44ee1f5c2d86

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Theorems.Thm_PI_FockOneDegW_Inner_wt_eq_wtN
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_support


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
theorem _root_.solution (F : MvPolynomial σ ℂ) :
    fockInner F F = ((∑ α ∈ F.support, Complex.normSq (coeff α F) * (wtN α : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_support, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.ofReal_natCast, wt_eq_wtN]
end PI.FockOneDegW.Inner
