-- Prove2me | solution 1 for PI.HwUniqW.bvec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:15.523801+00:00
-- url     : https://prove2.me/submissions/64eb70c4-70e3-4448-904d-1d9dcf4d7e40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) : bvec j i = if i = j then 1 else 0 := by
  simp only [bvec, Pi.single_apply]
end PI.HwUniqW
