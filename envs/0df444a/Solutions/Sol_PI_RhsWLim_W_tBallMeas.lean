-- Prove2me | solution 1 for PI.RhsWLim.W.tBallMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:19:21.240357+00:00
-- url     : https://prove2.me/submissions/aecad1a8-ef0e-487a-8046-2689729dba4d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Theorems.Thm_PI_RhsWLim_W_measurableSet_expBall

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
namespace PI.RhsWLim.W
theorem _root_.solution : TBallMeas := by
  intro k r m ρ
  have hc : Continuous (fun x : Mt k r => fun i j => (m⁻¹ * Matrix.of x) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact (measurableSet_expBall (k := k) (r := r) (UWb k r) ρ).preimage hc.measurable
end PI.RhsWLim.W
