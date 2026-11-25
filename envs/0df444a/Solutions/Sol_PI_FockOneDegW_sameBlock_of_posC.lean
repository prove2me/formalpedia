-- Prove2me | solution 1 for PI.FockOneDegW.sameBlock_of_posC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:08.005793+00:00
-- url     : https://prove2.me/submissions/3881ccfa-8d19-4a08-8aa8-9ddf319ce276

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
end PI.FockOneDegW
