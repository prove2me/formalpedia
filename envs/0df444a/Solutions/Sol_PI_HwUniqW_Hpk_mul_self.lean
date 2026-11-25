-- Prove2me | solution 1 for PI.HwUniqW.Hpk_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:05.466628+00:00
-- url     : https://prove2.me/submissions/92556d56-1f2c-4461-910f-099e6421c58f

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_piI_piI
import Theorems.Thm_PI_HwUniqW_epsI_piI
import Theorems.Thm_PI_HwUniqW_epsI_mul_self
import Theorems.Thm_PI_HwUniqW_Hpk_apply
import Theorems.Thm_PI_HwUniqW_Hpk_mul_apply

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
theorem _root_.solution : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [epsI_mul_self]
  · simp [h, Ne.symm h]
end PI.HwUniqW
