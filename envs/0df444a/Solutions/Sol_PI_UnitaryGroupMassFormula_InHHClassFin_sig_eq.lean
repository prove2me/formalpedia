-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.sig_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:30.713737+00:00
-- url     : https://prove2.me/submissions/e9519991-e8f2-464b-8bb9-bfa9931421e6

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
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) : (I.cm.sig : I.E →+* I.E) = starRingEnd I.E :=
  RingHom.ext fun _ => rfl
end PI.UnitaryGroupMassFormula.InHHClassFin
