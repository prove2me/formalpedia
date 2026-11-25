-- Prove2me | solution 1 for PI.RhsWLim.W.HU.inc_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:31.024235+00:00
-- url     : https://prove2.me/submissions/f06c3c24-fca9-4467-b21a-d02519c7e72b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq

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
theorem _root_.solution (a b : Gp k r) : inc (a * b) = lmulM (Matrix.of (inc a)) (inc b) := rfl
end PI.RhsWLim.W.HU
