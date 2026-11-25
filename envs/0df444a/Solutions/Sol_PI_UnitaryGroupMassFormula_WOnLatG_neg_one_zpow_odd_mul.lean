-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.WOnLatG.neg_one_zpow_odd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:08.357899+00:00
-- url     : https://prove2.me/submissions/e5c5d484-1b60-4f6c-97e4-7fec71881100

import Definitions.Def_Formalism_PeriodIntegrals_WOnLatG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilLatticeAction_NegOneZpowOddMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.WOnLatG
open PI.WPhDefs
namespace PI.UnitaryGroupMassFormula.WOnLatG
theorem _root_.solution {n : ℤ} (hn : Odd n) (m : ℤ) : (-1 : ℂ) ^ (n * m) = (-1 : ℂ) ^ m := by
  rw [zpow_mul, hn.neg_one_zpow]
end PI.UnitaryGroupMassFormula.WOnLatG
