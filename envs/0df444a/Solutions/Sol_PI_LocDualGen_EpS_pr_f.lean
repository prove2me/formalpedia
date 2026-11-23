-- Prove2me | solution 1 for PI.LocDualGen.EpS.pr_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:01.841541+00:00
-- url     : https://prove2.me/submissions/a95ac7bc-3624-46b8-9fb7-1f627ff143b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Theorems.Thm_PI_LocDualGen_EpS_pr_e

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
theorem _root_.solution : pr hr e he h0 h1 0 (1 - e) = 0 ∧ pr hr e he h0 h1 1 (1 - e) = 1 := by
  rw [map_sub, map_sub, map_one, map_one, (pr_e hr e he h0 h1).1, (pr_e hr e he h0 h1).2]
  simp
end PI.LocDualGen.EpS
