-- Prove2me | solution 1 for PI.RhsWLim.W.RI.map_jH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:56.810815+00:00
-- url     : https://prove2.me/submissions/0386920c-4009-4d0a-921b-d6dfeb4d04f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
import Theorems.Thm_PI_RhsWLim_W_RI_jH_memb
import Theorems.Thm_PI_RhsWLim_W_RI_range_jH

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
theorem _root_.solution {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).map (jH z') = μW' := by
  rw [(jH_memb z').map_comap, range_jH]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hW.2.2.1)
end PI.RhsWLim.W.RI
