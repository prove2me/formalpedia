-- Prove2me | solution 1 for PI.RhsWLim.W.opGen_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:41.557223+00:00
-- url     : https://prove2.me/submissions/3a57e7b4-d8b5-4033-b7a0-889e4edfad9b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (q : TrE k) :
    opGen k r q (wI k r (Fin.last k)) (wI k r (Fin.last k)) = (q none : ℂ) * Complex.I := by
  simp [opGen, wI]
end PI.RhsWLim.W
