-- Prove2me | solution 1 for PI.VolStabW.FFHS.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:21.469072+00:00
-- url     : https://prove2.me/submissions/11e1b1bd-a1b8-4f1d-a390-428de8638b26

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
theorem _root_.solution (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := LinearMap.mem_ker
end PI.VolStabW.FFHS
