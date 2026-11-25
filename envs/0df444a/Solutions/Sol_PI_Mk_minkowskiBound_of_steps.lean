-- Prove2me | solution 1 for PI.Mk.minkowskiBound_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:26.76091+00:00
-- url     : https://prove2.me/submissions/64e6cb8f-d3c9-436f-9c18-ff57dba91232

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_MinkowskiBoundOfSteps
import Theorems.Thm_PI_Mk_pGroupStep_of
import Theorems.Thm_PI_Mk_minkowskiBound_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset Polynomial
namespace PI.Mk
theorem _root_.solution (ha : TraceStep) (hb : PowerSumStep) : PI.MinkowskiBound :=
  minkowskiBound_of (pGroupStep_of ha hb)
end PI.Mk
