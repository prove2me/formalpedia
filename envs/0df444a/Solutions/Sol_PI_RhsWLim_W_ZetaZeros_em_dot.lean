-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.em_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:41.580518+00:00
-- url     : https://prove2.me/submissions/4149cab5-a137-4b34-913b-27236c8d725a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_MB_EmT_Em
import Theorems.Thm_PI_RhsWLim_W_MB_Em_conjT


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
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.ZetaZeros
theorem _root_.solution (u : Fin (k + 1) → ℂ) (Y : Fin (k + 1) → ℂ) :
    star (MB.Em k r *ᵥ u) ⬝ᵥ (MB.Em k r *ᵥ Y) = star u ⬝ᵥ Y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, MB.Em_conjT, MB.EmT_Em,
    Matrix.one_mulVec]
end PI.RhsWLim.W.ZetaZeros
