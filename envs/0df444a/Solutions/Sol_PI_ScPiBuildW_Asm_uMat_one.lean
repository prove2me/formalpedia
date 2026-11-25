-- Prove2me | solution 1 for PI.ScPiBuildW.Asm.uMat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:26:02.74481+00:00
-- url     : https://prove2.me/submissions/8d1e36cc-e8da-4211-b3ad-bf63fdf216c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_InnerOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped InnerProductSpace
open PI PI.ScPiBuildW PI.ScPiBuildW.Asm
open PI.ScPiExists Formalism.MainNotions.S
namespace PI.ScPiBuildW.Asm
theorem _root_.solution (I : AutInst) (v : InfinitePlace I.F) : uMat ((1 : I.Ginf) v) = 1 := rfl
end PI.ScPiBuildW.Asm
