-- Prove2me | solution 1 for PI.RhsWLim.W.RI.inv_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:21.194748+00:00
-- url     : https://prove2.me/submissions/26fe7d2d-efd4-471a-8961-d12d6dc3ce84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR

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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution {b : Mat k r} (hb : IsUnit b.det) {v : Fin (2 * r + k + 1) → ℂ} (h : b *ᵥ v = v) :
    b⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]
end PI.RhsWLim.W.RI
