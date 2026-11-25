-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.herm_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:25.562353+00:00
-- url     : https://prove2.me/submissions/5bf1aadc-9955-46ce-9fb5-6598dfad0573

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_inWb_eq
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_hpk_chain
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_em_dot

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
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (embWb k r μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← inWb_eq hz, ← inWb_eq hz']
  unfold herm
  rw [hpk_chain, em_dot]
end PI.RhsWLim.W.ZetaZeros
