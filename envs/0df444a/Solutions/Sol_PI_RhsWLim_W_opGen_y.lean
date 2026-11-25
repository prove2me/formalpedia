-- Prove2me | solution 1 for PI.RhsWLim.W.opGen_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:45.209305+00:00
-- url     : https://prove2.me/submissions/2b21f67e-0831-48e7-b896-c09a5a9f9fe0

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
theorem _root_.solution (q : TrE k) (a : Fin k) :
    opGen k r q (wI k r a.castSucc) (wI k r (Fin.last k)) = opBeta k q a := by
  simp [opGen, wI, a.isLt]
end PI.RhsWLim.W
