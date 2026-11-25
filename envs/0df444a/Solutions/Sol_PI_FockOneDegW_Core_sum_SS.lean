-- Prove2me | solution 1 for PI.FockOneDegW.Core.sum_SS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:35.53018+00:00
-- url     : https://prove2.me/submissions/662e327c-0399-4671-9fc6-61d89d06d28b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_sum_gg
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_left
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_right
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left


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
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (v : Pol p q r s)
    (hH : ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d v = 0) :
    ∑ a : Ix p q, ∑ b : Ix p q, SS v a b = 0 := by
  let F : Ix p q → Ix p q → Ix r s → Ix r s → ℂ :=
    fun a b c d => fockInner (gg v a c d) (gg v b c d)
  have h0 : ∑ c : Ix r s, ∑ d : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q, F a b c d = 0 := by
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    have e : ∑ a : Ix p q, ∑ b : Ix p q, F a b c d =
        fockInner (∑ a : Ix p q, gg v a c d) (∑ b : Ix p q, gg v b c d) := by
      rw [fockInner_sum_left]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [fockInner_sum_right]
    rw [e, sum_gg v hH c d, fockInner_zero_left]
  calc ∑ a : Ix p q, ∑ b : Ix p q, SS v a b
      = ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s, ∑ d : Ix r s, F a b c d := rfl
    _ = ∑ a : Ix p q, ∑ c : Ix r s, ∑ b : Ix p q, ∑ d : Ix r s, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q, ∑ d : Ix r s, F a b c d := Finset.sum_comm
    _ = ∑ c : Ix r s, ∑ a : Ix p q, ∑ d : Ix r s, ∑ b : Ix p q, F a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : Ix r s, ∑ d : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q, F a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = 0 := h0
end PI.FockOneDegW.Core
