-- Prove2me | solution 1 for PI.RhsWLim.W.HU.pull_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:46.536296+00:00
-- url     : https://prove2.me/submissions/a9e0600f-7d3f-4a3e-a3a8-1fcd4c7dcf49

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
theorem _root_.solution (μ : Measure (Mt k r)) (h : μ {x | Matrix.of x ∉ UWb k r} = 0) (s : Set (Mt k r)) :
    pull μ (inc ⁻¹' s) = μ s := by
  rw [pull, inc_memb.comap_apply, Set.image_preimage_eq_inter_range, range_inc]
  exact measure_inter_conull h
end PI.RhsWLim.W.HU
