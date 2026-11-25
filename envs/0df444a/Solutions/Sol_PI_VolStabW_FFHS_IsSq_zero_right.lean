-- Prove2me | solution 1 for PI.VolStabW.FFHS.IsSq.zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:56:33.050799+00:00
-- url     : https://prove2.me/submissions/b9666a06-d673-4cc2-b24d-9cbc6a0b4d17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS

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
theorem _root_.solution (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  simpa using hs.add_right x 0 0
end IsSq
end PI.VolStabW.FFHS
