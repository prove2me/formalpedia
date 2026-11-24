-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_J__eq_dcb540cc7f1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:26.552831+00:00
-- url     : https://prove2.me/submissions/d8c257d4-e74e-4c4e-a433-d677c7230b73

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
namespace Frame
theorem _root_.solution (fr : Frame I S) : fr.J' = fr.Jt.toBlocks₂₂ := rfl
end Frame
end PI.UnitaryGroupMassFormula.InHHClassFin
