-- Prove2me | solution 1 for PI.RhsWLim.W.sgn_wI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:16.033904+00:00
-- url     : https://prove2.me/submissions/34c159d0-c640-45f4-adca-979fb0f38f42

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
theorem _root_.solution (j : Fin (k + 1)) : HU.sgn k r (wI k r j) = if j = Fin.last k then -1 else 1 := by
  by_cases h : j = Fin.last k
  · subst h
    simp [PI.RhsWLim.W.HU.sgn, PI.RhsWLim.wI]
  · have hne : j.val ≠ k := fun e => h (Fin.ext (by rw [Fin.val_last]; exact e))
    simp [PI.RhsWLim.W.HU.sgn, PI.RhsWLim.wI, h, hne]
end PI.RhsWLim.W
