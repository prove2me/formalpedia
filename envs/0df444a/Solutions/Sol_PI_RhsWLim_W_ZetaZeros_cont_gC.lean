-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.cont_gC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:20.280448+00:00
-- url     : https://prove2.me/submissions/e7149df3-3ba0-48f9-8a95-db545cc3bbdb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_cont_emb

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
theorem _root_.solution : Continuous (gC k r) := by
  have hA : Continuous (fun p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r => (Matrix.of p.2.1 : Mat k r)) :=
    continuous_fst.comp continuous_snd
  have hB : Continuous (fun p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r =>
      embWb k r (Matrix.of p.1)) := cont_emb.comp continuous_fst
  have hC : Continuous (fun p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r => (Matrix.of p.2.2 : Mat k r)) :=
    continuous_snd.comp continuous_snd
  exact continuous_pi fun i => continuous_pi fun j => ((hA.matrix_mul hB).matrix_mul hC).matrix_elem i j
end PI.RhsWLim.W.ZetaZeros
