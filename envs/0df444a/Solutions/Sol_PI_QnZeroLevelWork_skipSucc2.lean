-- Prove2me | solution 1 for PI.QnZeroLevelWork.skipSucc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:49.759395+00:00
-- url     : https://prove2.me/submissions/4015386b-8dec-4548-8f18-9304f5b74566

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
import Theorems.Thm_PI_QnZeroLevelWork_skip_two_succAbove_comp_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnZeroLevelWork
theorem _root_.solution : SkipSucc2 := fun _ i i' j h => skip_two_succAbove_comp_alt i i' j h
end PI.QnZeroLevelWork
