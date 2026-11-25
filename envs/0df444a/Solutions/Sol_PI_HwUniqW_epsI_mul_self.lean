-- Prove2me | solution 1 for PI.HwUniqW.epsI_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:44.829808+00:00
-- url     : https://prove2.me/submissions/dfd249d6-cc00-4569-968e-92e923851ac0

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by
  unfold epsI
  split_ifs <;> norm_num
end PI.HwUniqW
