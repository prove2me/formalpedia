-- Prove2me | solution 1 for PI.UMultOne.UnitaryGroupMassFormula.uMultOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:17.750579+00:00
-- url     : https://prove2.me/submissions/4ea9cf85-ea4c-4798-8b71-f2e260d0aaef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
import Theorems.Thm_P2M_PI_UMultOne_UnitaryGroupMassFormula_uMultOne_of__89a6546dc0a4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set
namespace PI.UMultOne.UnitaryGroupMassFormula
theorem _root_.solution : ConjTranspose → GelfandCompact → CommutantMult → MultOne :=
  uMultOne_of'
end PI.UMultOne.UnitaryGroupMassFormula
