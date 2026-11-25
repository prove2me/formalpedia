-- Prove2me | solution 1 for PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:37.157923+00:00
-- url     : https://prove2.me/submissions/0293abf0-6572-4aff-8afb-5440d9d8bec5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Theorems.Thm_PI_FockOneDegW_Inner_wtN_pos
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
theorem _root_.solution (F : MvPolynomial σ ℂ) (h : (fockInner F F).re = 0) :
    F = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_re] at h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ ↦ mul_nonneg (Complex.normSq_nonneg (coeff α F)) (Nat.cast_nonneg (wtN α)))).1 h
  by_contra hF
  obtain ⟨α, hα⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF)
  have hc : coeff α F ≠ 0 := MvPolynomial.mem_support_iff.1 hα
  have hne : Complex.normSq (coeff α F) * (wtN α : ℝ) ≠ 0 :=
    mul_ne_zero (Complex.normSq_pos.2 hc).ne' (by exact_mod_cast (wtN_pos α).ne')
  exact hne (hall α hα)
end PI.FockOneDegW.Inner
