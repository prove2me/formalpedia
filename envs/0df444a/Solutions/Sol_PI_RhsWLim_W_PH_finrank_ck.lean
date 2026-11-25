-- Prove2me | solution 1 for PI.RhsWLim.W.PH.finrank_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:29.215712+00:00
-- url     : https://prove2.me/submissions/aa5a24c5-2002-4d3f-a710-3a0f6af5e9b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp

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
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH
namespace PI.RhsWLim.W.PH
theorem _root_.solution (k : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin k)), Complex.finrank_real_complex,
    finrank_euclideanSpace, Fintype.card_fin]
end PI.RhsWLim.W.PH
