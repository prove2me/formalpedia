-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:25.281911+00:00
-- url     : https://prove2.me/submissions/b88abe98-f557-49bc-aa37-01c31a924687

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
import Theorems.Thm_PI_RhsWLim_W_continuous_qf

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
theorem _root_.solution (T' : ℝ) : Continuous (tau k T') :=
  Real.continuous_sqrt.comp (continuous_qf.neg.div_const _)
end PI.RhsWLim.W
