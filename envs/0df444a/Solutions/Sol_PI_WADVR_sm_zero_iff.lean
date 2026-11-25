-- Prove2me | solution 1 for PI.WADVR.sm_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:00.511358+00:00
-- url     : https://prove2.me/submissions/92fc9bda-5579-49b6-8e19-ae29eeb97f00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_Sm_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}
namespace PI.WADVR
theorem _root_.solution {q : Q} : Sm Q ϖ 0 q ↔ q ∈ Set.range (algebraMap W Q) := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, by simp⟩
  · rintro ⟨c, rfl⟩; exact Sm.alg c
end PI.WADVR
