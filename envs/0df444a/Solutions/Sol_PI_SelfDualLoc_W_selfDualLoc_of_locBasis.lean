-- Prove2me | solution 1 for PI.SelfDualLoc.W.selfDualLoc_of_locBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:09.168432+00:00
-- url     : https://prove2.me/submissions/f3c19ccd-bf35-487a-a582-2d8f2ff19ce3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfLocBasis
import Theorems.Thm_PI_SelfDualLoc_W_selfDualLoc_of_steps
import Theorems.Thm_PI_SelfDualLoc_W_nondeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
namespace PI.SelfDualLoc.W
theorem _root_.solution (hL : LocBasis) : PI.SelfDualLoc :=
  selfDualLoc_of_steps nondeg hL
end PI.SelfDualLoc.W
