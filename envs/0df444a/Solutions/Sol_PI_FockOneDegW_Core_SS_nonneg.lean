-- Prove2me | solution 1 for PI.FockOneDegW.Core.SS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:28.191904+00:00
-- url     : https://prove2.me/submissions/79c4ef48-e7ba-43db-91c9-e51a70d7465a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_side_sb
import Theorems.Thm_PI_FockOneDegW_Core_posC_or
import Theorems.Thm_PI_FockOneDegW_Core_SS_swap
import Theorems.Thm_PI_FockOneDegW_Core_SS_self_nonneg
import Theorems.Thm_PI_FockOneDegW_Core_SS_offblock
import Theorems.Thm_PI_FockOneDegW_Core_SS_eq
import Theorems.Thm_PI_FockOneDegW_Core_hw_eq
import Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_re_nonneg


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
theorem _root_.solution (hK : OpsK) (μ : Ix p q → ℚ) (v : Pol p q r s)
    (hv : IsHW (fockAct1 p q r s) μ v) (a b : Ix p q) : 0 ≤ (SS v a b).re := by
  by_cases hab : a = b
  · subst hab; exact SS_self_nonneg v a
  by_cases hsb : sameBlock a b
  · rcases posC_or a b hsb hab with h | h
    · rw [SS_eq v a b hsb, hw_eq hK μ v hv a b h]
      exact fockInner_self_re_nonneg _
    · rw [SS_swap, Complex.conj_re, SS_eq v b a ((side_sb b a).2 ((side_sb a b).1 hsb).symm),
        hw_eq hK μ v hv b a h]
      exact fockInner_self_re_nonneg _
  · rw [SS_offblock v a b hsb]; simp
end PI.FockOneDegW.Core
