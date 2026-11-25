-- Prove2me | solution 1 for PI.RhsWLim.W.embWb_wI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:31.294256+00:00
-- url     : https://prove2.me/submissions/f689a7cd-12a9-4a02-a514-21a7df30f5fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest

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
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (j m : Fin (k + 1)) :
    embWb k r μ (wI k r j) (wI k r m) = μ j m := by
  have hj := j.isLt
  have hm := m.isLt
  have hc : (r ≤ (PI.RhsWLim.wI k r j).val ∧ (PI.RhsWLim.wI k r j).val ≤ r + k) ∧
      (r ≤ (PI.RhsWLim.wI k r m).val ∧ (PI.RhsWLim.wI k r m).val ≤ r + k) := by
    simp only [PI.RhsWLim.wI]
    omega
  unfold PI.RhsWLim.embWb
  rw [dif_pos hc]
  exact congrArg₂ μ (Fin.ext (by simp [PI.RhsWLim.wI])) (Fin.ext (by simp [PI.RhsWLim.wI]))
end PI.RhsWLim.W
