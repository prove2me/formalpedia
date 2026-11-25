-- Prove2me | solution 1 for PI.RhsWLim.W.RI.nu_conc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:47.487381+00:00
-- url     : https://prove2.me/submissions/aee1aac0-34a3-4080-9ac4-6b7112817dac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Theorems.Thm_PI_RhsWLim_W_HU_amb_closed
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_chartF
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_mem_chart
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_src_null


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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution (hD : WbData k r z z' μW μW' a a' μsec) :
    nuR k r z z' μW μW' μsec {x | Matrix.of x ∉ UWb k r} = 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
    HU.amb_closed.isOpen_compl.measurableSet]
  exact measure_mono_null (fun q hq hg => hq (mem_chart hD hg)) (src_null hD)
end PI.RhsWLim.W.RI
