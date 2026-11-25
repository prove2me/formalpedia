-- Prove2me | solution 1 for PI.RhsWLim.W.inv_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:39.462446+00:00
-- url     : https://prove2.me/submissions/ac310814-ed4a-440e-8895-bb6e3fe3c61d

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
theorem _root_.solution {h : Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) : h⁻¹ *ᵥ z = z := by
  obtain ⟨hU, -, hfix⟩ := hh
  have hdet := PI.RhsWLim.W.HU.isUnit_of_uh hU
  calc h⁻¹ *ᵥ z = h⁻¹ *ᵥ (h *ᵥ z) := by rw [hfix]
    _ = z := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul h hdet, Matrix.one_mulVec]
end PI.RhsWLim.W
