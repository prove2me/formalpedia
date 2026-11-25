-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.unitaryApproxFin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:16.145952+00:00
-- url     : https://prove2.me/submissions/f465c68f-b558-45fd-a454-bfb1294649b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (h1 : TopStep) (h2 : CayleyStep) (h3 : ApproxEStep)
    (hW : WeakApproxF) (hB : BddR) (hU : UnitS) (hE : EigAvoid) :
    PI.UnitaryApproxFin.UnitaryApproxFin :=
  h1 (h2 (h3 hW) hB hU) hE
end PI.UnitaryApproxFinWork
