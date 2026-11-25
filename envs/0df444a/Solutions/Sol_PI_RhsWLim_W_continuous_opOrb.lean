-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_opOrb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:50.785309+00:00
-- url     : https://prove2.me/submissions/af10bd46-2034-417e-aae4-a86327bb7f98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (T' : ℝ) : Continuous (opOrb k r T') := by
  have h : Continuous fun x : PI.RhsWLim.Mt k r => Matrix.of x *ᵥ opBase k r T' :=
    Continuous.matrix_mulVec (by exact continuous_id) continuous_const
  unfold opOrb opCo
  exact (continuous_pi fun i => (continuous_apply (PI.RhsWLim.wI k r (Fin.castSucc i))).comp h).prodMk
    ((continuous_apply (PI.RhsWLim.wI k r (Fin.last k))).comp h)
end PI.RhsWLim.W
