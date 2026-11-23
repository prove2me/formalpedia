-- Prove2me | solution 1 for PI.LocDualGen.EpS.pr_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:48.428798+00:00
-- url     : https://prove2.me/submissions/553d0534-fa6c-464d-a503-fd2d6bd48e79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpS
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)
namespace PI.LocDualGen.EpS
theorem _root_.solution (i : Fin 2) (z : L) : pr hr e he h0 h1 i z = (bas hr e he h0 h1).repr z i := rfl
end PI.LocDualGen.EpS
