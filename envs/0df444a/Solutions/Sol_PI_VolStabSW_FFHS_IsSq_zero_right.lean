-- Prove2me | solution 1 for PI.VolStabSW.FFHS.IsSq.zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:15.699313+00:00
-- url     : https://prove2.me/submissions/7e130a84-6707-4c5b-bba6-8ce42df5bea7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabSW.FFHS
namespace IsSq
theorem _root_.solution (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  have h0 := hs.smul_right 0 x 0
  simpa using h0
end IsSq
end PI.VolStabSW.FFHS
