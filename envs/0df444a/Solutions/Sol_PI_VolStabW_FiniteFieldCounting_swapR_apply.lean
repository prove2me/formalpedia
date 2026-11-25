-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldCounting.swapR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:56.322387+00:00
-- url     : https://prove2.me/submissions/86100010-d030-4b5d-a237-04c41c241ae1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldCounting
namespace PI.VolStabW.FiniteFieldCounting
theorem _root_.solution (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl
end PI.VolStabW.FiniteFieldCounting
