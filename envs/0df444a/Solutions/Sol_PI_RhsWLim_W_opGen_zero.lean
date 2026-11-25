-- Prove2me | solution 1 for PI.RhsWLim.W.opGen_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:52:39.788969+00:00
-- url     : https://prove2.me/submissions/aec84a3e-8106-456f-ac7e-65d70ef0e2f8

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
theorem _root_.solution : opGen k r (0 : TrE k) = 0 := (opGenLin k r).map_zero
end PI.RhsWLim.W
