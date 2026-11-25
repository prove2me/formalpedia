-- Prove2me | solution 1 for PI.RhsWLim.W.HU.map_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:40.152644+00:00
-- url     : https://prove2.me/submissions/2be50e15-aa8f-4a18-b241-4ef4008808d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Theorems.Thm_PI_RhsWLim_W_HU_inc_memb
import Theorems.Thm_PI_RhsWLim_W_HU_range_inc

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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.HU
theorem _root_.solution (μ : Measure (Mt k r)) (h : μ {x | Matrix.of x ∉ UWb k r} = 0) : (pull μ).map inc = μ := by
  rw [pull, inc_memb.map_comap, range_inc]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h)
end PI.RhsWLim.W.HU
