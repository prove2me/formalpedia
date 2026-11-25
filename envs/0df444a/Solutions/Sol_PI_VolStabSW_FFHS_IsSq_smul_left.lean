-- Prove2me | solution 1 for PI.VolStabSW.FFHS.IsSq.smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:08.900986+00:00
-- url     : https://prove2.me/submissions/2133f492-de7e-41d0-bf4b-e909c71b3e71

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
theorem _root_.solution (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]
end IsSq
end PI.VolStabSW.FFHS
