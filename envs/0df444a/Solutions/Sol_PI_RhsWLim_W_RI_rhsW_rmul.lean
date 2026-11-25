-- Prove2me | solution 1 for PI.RhsWLim.W.RI.rhsW_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:22.898584+00:00
-- url     : https://prove2.me/submissions/b93247d0-b768-41e5-acc3-d26bba89b0bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Theorems.Thm_PI_RhsWLim_W_RI_inner_r

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
theorem _root_.solution (hd : WbData k r z z' μW μW' a a' μsec) (b : Mat k r) (hb : b ∈ UWset k r z')
    (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    rhsW k r z z' μW μW' μsec (fun x => φ (rmulM b x)) = rhsW k r z z' μW μW' μsec φ := by
  unfold rhsW
  refine lintegral_congr fun ζ => ?_
  congr 1
  refine lintegral_congr fun h => ?_
  exact inner_r hd.haarW' _ φ hφ b hb
end PI.RhsWLim.W.RI
