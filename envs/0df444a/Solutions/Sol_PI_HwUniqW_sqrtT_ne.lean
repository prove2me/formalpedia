-- Prove2me | solution 1 for PI.HwUniqW.sqrtT_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:40.941944+00:00
-- url     : https://prove2.me/submissions/e48a624a-b2a3-4285-86da-e80b398b7a63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) :
    (((Real.sqrt (Tz k r z) : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hT).ne'
end PI.HwUniqW
