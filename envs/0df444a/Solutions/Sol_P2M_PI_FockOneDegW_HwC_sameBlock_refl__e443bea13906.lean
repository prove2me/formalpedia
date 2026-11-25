-- Prove2me | solution 1 for P2M_PI_FockOneDegW_HwC_sameBlock_refl__e443bea13906
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:18.169807+00:00
-- url     : https://prove2.me/submissions/c4095a23-1463-4e8b-8be3-7b3dda2d1322

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.HwC
namespace PI.FockOneDegW.HwC
theorem _root_.solution {p q : ℕ} (c : Ix p q) : sameBlock c c := by
  cases c <;> trivial
end PI.FockOneDegW.HwC
