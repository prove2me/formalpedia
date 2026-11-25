-- Prove2me | solution 1 for PI.HwUniqW.Hpk_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:10.987725+00:00
-- url     : https://prove2.me/submissions/6e578e2d-1b95-4d8b-8516-13f21050d314

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
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
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (i) :
    (Hpk k r *ᵥ v) i = epsI k r i * v (piI k r i) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (piI k r i)]
  · rw [Hpk_apply, if_pos rfl]
  · intro l hl
    rw [Hpk_apply, if_neg hl, zero_mul]
end PI.HwUniqW
