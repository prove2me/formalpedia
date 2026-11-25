-- Prove2me | solution 1 for PI.RhsWLim.W.GE.lie_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:19.428457+00:00
-- url     : https://prove2.me/submissions/2551c821-15ff-4293-a571-a9a9816d2415

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
import Theorems.Thm_PI_RhsWLim_W_GE_dg_mem
import Theorems.Thm_PI_RhsWLim_W_GE_exp_dV
import Theorems.Thm_PI_RhsWLim_W_GE_unit_exp

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
theorem _root_.solution : Nontrivial (lieE (UWb k r)) := by
  rw [Submodule.nontrivial_iff_ne_bot, Submodule.ne_bot_iff]
  refine ⟨(WithLp.equiv 2 _).symm (realifyFun (diagonal (dV k r))), Submodule.subset_span
    ⟨diagonal (dV k r), (show diagonal (dV k r) ∈ lieOf (UWb k r) from fun t => by
      rw [exp_dV]
      exact dg_mem _ (unit_exp t)), rfl⟩, ?_⟩
  intro h
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) =>
    x (p0 k r, p0 k r, true)) h
  simp [realifyFun, dV] at h1
end PI.RhsWLim.W.GE
