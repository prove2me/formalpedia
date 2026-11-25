-- Prove2me | solution 1 for PI.WADVR.sm_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:41.050403+00:00
-- url     : https://prove2.me/submissions/6c939cab-4b37-4815-ac21-949134a082fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_sm_one_of_not_isUnit

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
theorem _root_.solution (hϖ : Irreducible ϖ) {p : ℕ} (hp : ¬ IsUnit (p : W)) : Sm Q ϖ 1 (p : Q) := by
  have := sm_one_of_not_isUnit (Q := Q) hϖ hp
  rwa [map_natCast] at this
end PI.WADVR
