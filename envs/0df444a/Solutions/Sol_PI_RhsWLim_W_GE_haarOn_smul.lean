-- Prove2me | solution 1 for PI.RhsWLim.W.GE.haarOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:04.836389+00:00
-- url     : https://prove2.me/submissions/a6720759-90f7-413d-990b-9b0be3cd73db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists

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
theorem _root_.solution (S : Set (Mat k r)) (ν : Measure (Mt k r)) (c : ℝ≥0) (hc : c ≠ 0) (h : IsHaarOn S ν) :
    IsHaarOn S (c • ν) := by
  refine ⟨?_, ?_, ?_, fun s hs => ?_⟩
  · have := h.1
    infer_instance
  · intro h0
    apply h.2.1
    rw [← Measure.measure_univ_eq_zero]
    have h1 := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simpa [hc] using h1
  · rw [Measure.smul_apply, h.2.2.1, smul_zero]
  · rw [Measure.map_smul, h.2.2.2 s hs]
end PI.RhsWLim.W.GE
