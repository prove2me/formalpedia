-- Prove2me | solution 1 for PI.TOW.LiftW.pderiv_embS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:06.836809+00:00
-- url     : https://prove2.me/submissions/fe1a3a95-e628-449d-97af-999d6c6b7462

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
import Theorems.Thm_PI_TOW_LiftW_inj

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
theorem _root_.solution (t : Fin n') (b : Fin k) (W : MvPolynomial (Fin k) K) :
    pderiv (t, b) (embS K t W) = embS K t (pderiv b W) := by
  simpa [embS] using pderiv_rename (inj (k := k) t) b W
end PI.TOW.LiftW
