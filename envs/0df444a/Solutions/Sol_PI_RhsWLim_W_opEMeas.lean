-- Prove2me | solution 1 for PI.RhsWLim.W.opEMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:25.232091+00:00
-- url     : https://prove2.me/submissions/a708d952-4982-4929-a7e3-d52db7bfe78c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Theorems.Thm_PI_RhsWLim_W_continuous_opEmap

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
theorem _root_.solution : OpEMeas := by

  intro k r T' ρ
  unfold opE
  have hball : Metric.ball (0 : TrE k) ρ = ⋃ n : ℕ, Metric.closedBall 0 (ρ - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Metric.mem_ball, Metric.mem_closedBall, Set.mem_iUnion, dist_zero_right]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hball, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun n => ?_)
  exact ((isCompact_closedBall _ _).image (continuous_opEmap k r T')).isClosed.measurableSet
end PI.RhsWLim.W
