-- Prove2me | solution 1 for PI.RhsWLim.W.RI.orbV_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:28.492009+00:00
-- url     : https://prove2.me/submissions/6c045498-df1e-444a-a1a5-18cd44c9797b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv

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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution (z' : Fin (2 * r + k + 1) → ℂ) : Continuous (orbV k r z') := by
  unfold orbV
  exact Continuous.matrix_mulVec (continuous_id' (X := Mt k r)) continuous_const
end PI.RhsWLim.W.RI
