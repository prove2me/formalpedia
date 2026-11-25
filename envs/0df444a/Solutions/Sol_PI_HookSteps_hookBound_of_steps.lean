-- Prove2me | solution 1 for PI.HookSteps.hookBound_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:58.986075+00:00
-- url     : https://prove2.me/submissions/fe4d0f3f-d4f3-49a1-8792-6ba002252638

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookBoundOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution (hB : HookBoundOf) (hN : HookNormOf) (hS : DetShiftNormOf)
    (hR : RenameIso) (hH : HwDetMul) (hL : HwLastZero) (hA : DetAdj) (hD : DetDetId)
    (hP : PolEqRowDiv) : PI.HookBound :=
  hB (hN hR hH hL (hS hA hD hP hH))
end PI.HookSteps
