-- Prove2me | solution 1 for PI.SelfDualLoc.W.selfDualLoc_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:29.448377+00:00
-- url     : https://prove2.me/submissions/a14b2a9f-fbc4-4ce1-b1f1-b4ab990592af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfLocBasis
import Theorems.Thm_PI_SelfDualLoc_W_dualBasis
import Theorems.Thm_PI_SelfDualLoc_W_selfDualLoc_of
import Theorems.Thm_PI_SelfDualLoc_W_sigInt
import Theorems.Thm_PI_SelfDualLoc_W_spanTop_of
import Theorems.Thm_PI_SelfDualLoc_W_unitLoc


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
theorem _root_.solution (hN : Nondeg) (hL : LocBasis) : PI.SelfDualLoc :=
  selfDualLoc_of sigInt hN (spanTop_of hN) hL dualBasis unitLoc
end PI.SelfDualLoc.W
