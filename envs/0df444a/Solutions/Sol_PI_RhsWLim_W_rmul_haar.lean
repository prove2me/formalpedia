-- Prove2me | solution 1 for PI.RhsWLim.W.rmul_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:33.409825+00:00
-- url     : https://prove2.me/submissions/f9ecbd4f-4162-4bb6-a5f3-6c8c77ed21c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS
import Theorems.Thm_PI_RhsWLim_W_lr_comm
import Theorems.Thm_PI_RhsWLim_W_HU_amb_closed
import Theorems.Thm_PI_RhsWLim_W_HU_lmulM_cont
import Theorems.Thm_PI_RhsWLim_W_rmulM_meas


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim HU
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r) :
    IsHaarOn (UWb k r) (ν.map (rmulM p)) := by
  obtain ⟨hσ, h0, hc, hl⟩ := hH
  have hu := uwb_unit hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rmulE p hu).sigmaFinite_map
  · rw [Ne, Measure.map_eq_zero_iff (rmulM_meas p).aemeasurable]; exact h0
  · have hms : MeasurableSet {x : Mt k r | Matrix.of x ∉ UWb k r} := amb_closed.isOpen_compl.measurableSet
    rw [Measure.map_apply (rmulM_meas p) hms]
    refine measure_mono_null (fun x hx => ?_) hc
    intro hxm
    apply hx
    show Matrix.of x * p ∈ UWb k r
    exact uwb_mul hxm hp
  · intro s hs
    rw [Measure.map_map (lmulM_cont s).measurable (rmulM_meas p), lr_comm,
      ← Measure.map_map (rmulM_meas p) (lmulM_cont s).measurable, hl s hs]
end PI.RhsWLim.W
