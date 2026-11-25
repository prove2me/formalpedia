-- Prove2me | solution 1 for PI.TOW.LiftW.inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:16.803833+00:00
-- url     : https://prove2.me/submissions/ad3cd5c1-5e26-424a-8158-ace77417e702

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW PI.TOW.LiftW
open PI.TO PI.TOW
variable {K : Type} [CommRing K] {n' k : ℕ}
namespace PI.TOW.LiftW
theorem _root_.solution (t : Fin n') : Function.Injective (fun c : Fin k => (t, c)) := by
  intro a c h
  exact (Prod.mk.inj h).2
end PI.TOW.LiftW
