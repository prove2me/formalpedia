-- Prove2me | solution 1 for PI.EF.log_two_le_LL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:55.271698+00:00
-- url     : https://prove2.me/submissions/98b70c5e-6308-4b79-b1db-1555a7998382

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_two_le_arg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (N : ℕ) [NeZero N] (t : ℝ) : Real.log 2 ≤ LL N t := Real.log_le_log (by norm_num) (two_le_arg N t)
end PI.EF
