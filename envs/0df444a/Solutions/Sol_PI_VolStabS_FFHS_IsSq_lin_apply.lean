-- Prove2me | solution 1 for PI.VolStabS.FFHS.IsSq.lin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:39.523093+00:00
-- url     : https://prove2.me/submissions/26158f2d-e3a3-4605-9715-d834a9d289a2

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
theorem _root_.solution (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl
end IsSq
end PI.VolStabS.FFHS
