-- Prove2me | solution 1 for PI.ScRefExists.GlueA.incl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:23.754185+00:00
-- url     : https://prove2.me/submissions/5e128a58-437d-4975-be98-9d4c021d04bf

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
theorem _root_.solution (x : Fin I.n → I.E) (i : Fin I.n) :
    incl I x i = Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := rfl
end PI.ScRefExists.GlueA
