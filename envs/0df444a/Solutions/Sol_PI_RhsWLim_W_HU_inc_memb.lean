-- Prove2me | solution 1 for PI.RhsWLim.W.HU.inc_memb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:38:22.92292+00:00
-- url     : https://prove2.me/submissions/2ef6dda5-6e5d-4c64-835d-94f8585954c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Theorems.Thm_PI_RhsWLim_W_HU_amb_closed

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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.HU
theorem _root_.solution : MeasurableEmbedding (inc : Gp k r → Mt k r) :=
  MeasurableEmbedding.subtype_coe amb_closed.measurableSet
end PI.RhsWLim.W.HU
