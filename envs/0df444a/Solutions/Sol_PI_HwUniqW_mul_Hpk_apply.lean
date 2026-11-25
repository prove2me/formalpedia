-- Prove2me | solution 1 for PI.HwUniqW.mul_Hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:33.061419+00:00
-- url     : https://prove2.me/submissions/305d51c1-7428-4aa2-b085-3bf0745ffd09

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_piI_piI
import Theorems.Thm_PI_HwUniqW_epsI_piI
import Theorems.Thm_PI_HwUniqW_Hpk_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (piI k r j) * epsI k r j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (piI k r j)]
  · rw [Hpk_apply, if_pos (piI_piI j).symm, epsI_piI]
  · intro l hl
    rw [Hpk_apply, if_neg, mul_zero]
    intro h
    apply hl
    rw [h, piI_piI]
end PI.HwUniqW
