-- Prove2me | solution 2 for PI.BesselDerivW.liftA_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:16:09.528389+00:00
-- url     : https://prove2.me/submissions/07e093b6-bbe4-48cf-b526-ded29072a57e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_LiftAOneZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
open PI PI.BesselDerivW
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PI.BesselDerivW
theorem _root_.solution (a : E →L[ℝ] E) (p : ℝ × E) : liftA a p = (0, a p.2) := rfl
end PI.BesselDerivW
