-- Prove2me | solution 1 for PI.RhsWLim.W.RI.range_jH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:26.736523+00:00
-- url     : https://prove2.me/submissions/6a3f7e3c-3fd4-4f25-8077-be18bde33b9b

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
theorem _root_.solution (z' : Fin (2 * r + k + 1) → ℂ) :
    range (jH (k := k) (r := r) z') = {x | Matrix.of x ∈ UWset k r z'} := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact jH_mem z' h
  · intro hx
    exact ⟨⟨⟨x, ⟨hx.1, hx.2.1⟩⟩, hx.2.2⟩, rfl⟩
end PI.RhsWLim.W.RI
