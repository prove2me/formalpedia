-- Prove2me | solution 1 for PI.RhsWLim.W.phiT_coord_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:34.56855+00:00
-- url     : https://prove2.me/submissions/df80a91f-55b7-4a71-9ef4-2fdb10b75926

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
theorem _root_.solution (T' : ℝ) (q : TrE k) :
    phiT k r T' q none = (Complex.log (psiV k r T' q (wI k r (Fin.last k)))).im := by
  rw [Complex.log_im]; rfl
end PI.RhsWLim.W
