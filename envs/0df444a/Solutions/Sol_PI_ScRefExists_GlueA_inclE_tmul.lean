-- Prove2me | solution 1 for PI.ScRefExists.GlueA.inclE_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:00.837675+00:00
-- url     : https://prove2.me/submissions/e945cf60-d560-4abf-8b23-e1c2d2c898f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GlueA
theorem _root_.solution (a : I.E) : Formalism.UG.inclE (F := I.F) (Af I.F) a = a ⊗ₜ[I.F] (1 : Af I.F) := rfl
end PI.ScRefExists.GlueA
