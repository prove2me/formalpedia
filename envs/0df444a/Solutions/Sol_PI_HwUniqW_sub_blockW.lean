-- Prove2me | solution 1 for PI.HwUniqW.sub_blockW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:14:31.272896+00:00
-- url     : https://prove2.me/submissions/525dab2e-f35e-4fc2-8634-df78dff970cd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_blockW_bl

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
theorem _root_.solution (h : Matrix (Fin k) (Fin k) ℂ) : sub k r (blockW k r h) = h := by
  funext a b
  exact blockW_bl h a b
end PI.HwUniqW
