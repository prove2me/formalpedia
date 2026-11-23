-- Prove2me | solution 1 for PI.LocDualGen.EpS.isIntegral_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:31.502251+00:00
-- url     : https://prove2.me/submissions/759732c3-4802-4651-8edb-0d5b856a3a7b

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
variable [ValuativeRel K]
namespace PI.LocDualGen.EpS
theorem _root_.solution (e : L) (he : IsIdempotentElem e) : IsIntegral 𝒪[K] e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub (by simp)
  · simp [pow_two, he.eq]
end PI.LocDualGen.EpS
