-- Prove2me | solution 1 for PI.RhsWLim.W.GE.tBall_mass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:22.284096+00:00
-- url     : https://prove2.me/submissions/0e03d4ed-0c32-4cba-bbd6-e9ca9eeea8d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
import Theorems.Thm_PI_RhsWLim_W_HU_lmulM_cont
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
open scoped ENNReal NNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.GE
variable {k r : ℕ}
namespace PI.RhsWLim.W.GE
theorem _root_.solution (ν : Measure (Mt k r)) (h : IsHaarOn (UWb k r) ν) (m : Mat k r) (hm : m ∈ UWb k r) (ρ : ℝ) :
    ν (tBall k r m ρ) = ν (bBall k r ρ) := by
  have hinv := HU.uwb_inv hm
  have hB : MeasurableSet (bBall k r ρ) := measurableSet_expBall k r (UWb k r) ρ
  calc ν (tBall k r m ρ) = ν (lmulM m⁻¹ ⁻¹' bBall k r ρ) := rfl
    _ = (ν.map (lmulM m⁻¹)) (bBall k r ρ) := (Measure.map_apply (HU.lmulM_cont _).measurable hB).symm
    _ = ν (bBall k r ρ) := by rw [h.2.2.2 _ hinv]
end PI.RhsWLim.W.GE
