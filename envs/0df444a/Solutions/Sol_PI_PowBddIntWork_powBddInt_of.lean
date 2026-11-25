-- Prove2me | solution 1 for PI.PowBddIntWork.powBddInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:36.260418+00:00
-- url     : https://prove2.me/submissions/b738f14e-116b-480b-a541-1eba12b8dfb0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PowBddInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PowBddIntWork
open Matrix
namespace PI.PowBddIntWork
theorem _root_.solution (ha : StepA) (hb : StepB) : PI.PowBddInt := by
  intro E _ _ k γ N hN h i
  exact hb E k γ (ha E k γ N hN h) i
end PI.PowBddIntWork
