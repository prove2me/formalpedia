-- Prove2me | solution 1 for PI.VolStabS.FFHS.IsSq.zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:24.864114+00:00
-- url     : https://prove2.me/submissions/2593edf7-dcdf-4926-accb-5aa0f78ef08e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_zero_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabS.FFHS
namespace IsSq
theorem _root_.solution (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]
end IsSq
end PI.VolStabS.FFHS
