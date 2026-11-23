-- Prove2me | solution 1 for PI.VolStabW.FFHS.IsSq.lin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:04.272809+00:00
-- url     : https://prove2.me/submissions/171a1b3c-df15-451a-b889-a03b19ee7860

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
theorem _root_.solution (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl
end IsSq
end PI.VolStabW.FFHS
