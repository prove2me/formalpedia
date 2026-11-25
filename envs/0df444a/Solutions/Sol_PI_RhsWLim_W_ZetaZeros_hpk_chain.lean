-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.hpk_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:40.544457+00:00
-- url     : https://prove2.me/submissions/f8e3294b-feb2-45ec-86bb-cba82e64b6c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_emb_mul_Em
import Theorems.Thm_PI_RhsWLim_W_MB_Hpk_Em


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
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    Hpk k r *ᵥ (embWb k r μ *ᵥ (MB.Em k r *ᵥ u)) = MB.Em k r *ᵥ (Hb k *ᵥ (μ *ᵥ u)) := by
  rw [Matrix.mulVec_mulVec u (embWb k r μ) (MB.Em k r), emb_mul_Em, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ (Hpk k r) (MB.Em k r), MB.Hpk_Em, ← Matrix.mulVec_mulVec]
end PI.RhsWLim.W.ZetaZeros
