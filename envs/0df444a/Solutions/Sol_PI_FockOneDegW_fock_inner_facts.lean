-- Prove2me | solution 1 for PI.FockOneDegW.fock_inner_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:31.894915+00:00
-- url     : https://prove2.me/submissions/eebbb461-1341-4bb2-8d01-6706545c9f5c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_re_nonneg
import Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_im
import Theorems.Thm_PI_FockOneDegW_Inner_eq_zero_of_fockInner_self_re
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right
import Theorems.Thm_FockRaiseLowInner_fockInner_swap


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
open PI PI.FockOneDegW
open PI.FockOneDegW.Inner
namespace PI.FockOneDegW
theorem _root_.solution : InnerFacts := by
  intro σ P Q Q' c
  refine ⟨fockInner_add_right _ _ _, fockInner_smul_right _ _ _, fockInner_swap _ _,
    ⟨fockInner_self_im _, fockInner_self_re_nonneg _⟩, fun h ↦ ?_, fun l ↦ fockInner_X_mul l P Q⟩
  exact eq_zero_of_fockInner_self_re P (by rw [h]; simp)
end PI.FockOneDegW
