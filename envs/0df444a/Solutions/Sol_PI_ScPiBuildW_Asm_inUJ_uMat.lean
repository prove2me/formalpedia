-- Prove2me | solution 1 for PI.ScPiBuildW.Asm.inUJ_uMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:14.826539+00:00
-- url     : https://prove2.me/submissions/dca4fb02-f34f-4e7a-8e96-4ba7e99ab561

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
theorem _root_.solution (I : AutInst) (s : I.Ginf) (v : InfinitePlace I.F) : Formalism.REAL.inUJ (I.ε v) (uMat (s v)) :=
  (s v).2
end PI.ScPiBuildW.Asm
