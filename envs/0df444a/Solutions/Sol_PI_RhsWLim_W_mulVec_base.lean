-- Prove2me | solution 1 for PI.RhsWLim.W.mulVec_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:45.445394+00:00
-- url     : https://prove2.me/submissions/175f6cdd-55e2-4854-8012-1ee8f2ca7f22

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
theorem _root_.solution (T' : ℝ) (M : Mat k r) (i : Fin (2 * r + k + 1)) :
    (M *ᵥ opBase k r T') i = (Real.sqrt T' : ℂ) * M i (wI k r (Fin.last k)) := by
  simp [opBase, wLast, bvec, Matrix.mulVec_smul]
end PI.RhsWLim.W
