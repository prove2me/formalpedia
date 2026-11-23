-- Prove2me | solution 1 for PI.VolStabS.FFHS.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:36.041577+00:00
-- url     : https://prove2.me/submissions/bf5898b3-83c6-419d-9663-39a54e3111b9

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
theorem _root_.solution (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := LinearMap.mem_ker
end PI.VolStabS.FFHS
