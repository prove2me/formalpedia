-- Prove2me | solution 1 for TwistedEisensteinNonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:18.958943+00:00
-- url     : https://prove2.me/submissions/9d6d1953-9b16-434b-bd7f-576de733a995

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TwistedEisensteinOfRemaining
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TwistedEisensteinNonvanishing
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_bounded_matrix_entries
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_test_function_periodicity
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_test_function_support
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_twisted_eisenstein_of_remaining


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing :=
  PI.TwistedEisensteinNonvanishing.W.twisted_eisenstein_of_remaining PI.TwistedEisensteinNonvanishing.W.test_function_support PI.TwistedEisensteinNonvanishing.W.test_function_periodicity PI.TwistedEisensteinNonvanishing.W.bounded_matrix_entries
