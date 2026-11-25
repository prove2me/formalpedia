-- Prove2me | solution 1 for PI.UnitKronW.stepB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:36.177891+00:00
-- url     : https://prove2.me/submissions/09ec0776-0c0b-4752-8b37-7f3fb44b7335

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_IntRootProp
import Theorems.Thm_PI_UnitKronW_stepB_of
import Theorems.Thm_PI_UnitKronW_intRootProp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Polynomial
namespace PI.UnitKronW
theorem _root_.solution : StepB :=
  stepB_of intRootProp
end PI.UnitKronW
