-- Prove2me | solution 1 for PI.RhsWLim.W.measurableSet_expBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:44:57.014782+00:00
-- url     : https://prove2.me/submissions/0b99bace-5157-44a4-8ba8-5e5cbf8bbf9f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Theorems.Thm_PI_RhsWLim_W_continuous_expChart

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
theorem _root_.solution (k r : ℕ) (S : Set (Mat k r)) (ρ : ℝ) :
    MeasurableSet (expBall (k := k) (r := r) S ρ) := by
  have hball : IsSigmaCompact (Metric.ball (0 : lieE S) ρ) :=
    isSigmaCompact_iff_sigmaCompactSpace.2
      (haveI : LocallyCompactSpace (Metric.ball (0 : lieE S) ρ) := Metric.isOpen_ball.locallyCompactSpace
       inferInstance)
  obtain ⟨K, hK, hKU⟩ := hball.image (continuous_expChart k r S)
  unfold expBall
  rw [← hKU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet
end PI.RhsWLim.W
