-- Prove2me | solution 1 for PI.VolStabS.FFHS.IsSq.zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:56.609873+00:00
-- url     : https://prove2.me/submissions/66a967d6-9372-48c1-8ddd-83d87f29bb8d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS

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
theorem _root_.solution (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  simpa using hs.add_right x 0 0
end IsSq
end PI.VolStabS.FFHS
