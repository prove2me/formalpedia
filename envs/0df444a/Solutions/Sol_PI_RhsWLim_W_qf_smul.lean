-- Prove2me | solution 1 for PI.RhsWLim.W.qf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:04.288463+00:00
-- url     : https://prove2.me/submissions/f346be09-ca7e-4771-8f80-26237c615531

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
import Theorems.Thm_PI_RhsWLim_W_normSq_real_smul

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
variable {k : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (t : ℝ) (p : (Fin k → ℂ) × ℂ) : qf k (t • p) = t ^ 2 * qf k p := by
  unfold qf
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, normSq_real_smul, ← Finset.mul_sum]
  ring
end PI.RhsWLim.W
