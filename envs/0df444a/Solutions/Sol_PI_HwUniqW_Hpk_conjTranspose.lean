-- Prove2me | solution 1 for PI.HwUniqW.Hpk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:59:31.708662+00:00
-- url     : https://prove2.me/submissions/935ed5e6-d701-4df9-bc12-26d9209cb335

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_piI_piI
import Theorems.Thm_PI_HwUniqW_epsI_piI
import Theorems.Thm_PI_HwUniqW_star_epsI
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
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = piI k r i
  · subst h
    rw [piI_piI, if_pos rfl, if_pos rfl, star_epsI, epsI_piI]
  · have h' : ¬ i = piI k r j := fun h' => h (by rw [h', piI_piI])
    rw [if_neg h', if_neg h, star_zero]
end PI.HwUniqW
