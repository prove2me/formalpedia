-- Prove2me | solution 1 for PI.RhsWLim.W.RI.pull_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:22.998407+00:00
-- url     : https://prove2.me/submissions/19f3a8fd-1c37-47ef-8e7a-117951e92886

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
import Theorems.Thm_PI_RhsWLim_W_RI_jH_mem
import Theorems.Thm_PI_RhsWLim_W_HU_inc_memb
import Theorems.Thm_PI_RhsWLim_W_HU_map_pull
import Theorems.Thm_PI_RhsWLim_W_RI_rmulM_cont


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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W
variable {k r : ℕ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution {z' : Fin (2 * r + k + 1) → ℂ} (ν : Measure (Mt k r))
    (hc : ν {x | Matrix.of x ∉ UWb k r} = 0) (hr : ∀ b ∈ UWset k r z', ν.map (rmulM b) = ν)
    (g : stabH k r z') : (HU.pull ν).map (· * (g : HU.Gp k r)) = HU.pull ν := by
  have hg : Measurable (fun h : HU.Gp k r => h * (g : HU.Gp k r)) := (continuous_mul_const _).measurable
  have e : (HU.inc ∘ fun h : HU.Gp k r => h * (g : HU.Gp k r)) = rmulM (Matrix.of (jH z' g)) ∘ HU.inc :=
    funext fun h => rfl
  calc (HU.pull ν).map (· * (g : HU.Gp k r))
      = (((HU.pull ν).map (· * (g : HU.Gp k r))).map HU.inc).comap HU.inc := (HU.inc_memb.comap_map _).symm
    _ = (((HU.pull ν).map HU.inc).map (rmulM (Matrix.of (jH z' g)))).comap HU.inc := by
        rw [Measure.map_map HU.inc_memb.measurable hg, e,
          ← Measure.map_map (rmulM_cont _).measurable HU.inc_memb.measurable]
    _ = ((HU.pull ν).map HU.inc).comap HU.inc := by
        rw [HU.map_pull ν hc, hr _ (jH_mem z' g)]
    _ = HU.pull ν := HU.inc_memb.comap_map _
end PI.RhsWLim.W.RI
