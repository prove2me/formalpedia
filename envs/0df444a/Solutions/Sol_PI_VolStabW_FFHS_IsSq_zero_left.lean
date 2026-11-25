-- Prove2me | solution 1 for PI.VolStabW.FFHS.IsSq.zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:40.377166+00:00
-- url     : https://prove2.me/submissions/f51efa80-e201-4664-8c57-d06bcbf8ad0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabW_FFHS_IsSq_zero_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabW.FFHS
namespace IsSq
theorem _root_.solution (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]
end IsSq
end PI.VolStabW.FFHS
