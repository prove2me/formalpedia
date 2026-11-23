-- Prove2me | solution 1 for PI.LocDualGen.EpS.pr_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:04.898476+00:00
-- url     : https://prove2.me/submissions/4c4635e1-48c8-4b06-be19-ab9ac412d2b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Theorems.Thm_PI_LocDualGen_EpS_pr_apply

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
theorem _root_.solution : pr hr e he h0 h1 0 e = 1 ∧ pr hr e he h0 h1 1 e = 0 := by
  have : e = (1 : K) • e + (0 : K) • (1 - e) := by simp
  have key := repr_pair hr e he h0 h1 1 0
  rw [← this] at key
  rw [pr_apply, pr_apply]; exact key
end PI.LocDualGen.EpS
