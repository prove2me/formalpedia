-- Prove2me | solution 1 for PI.WADVR.sm_of_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:35.067187+00:00
-- url     : https://prove2.me/submissions/75a143a2-34ba-48de-9612-fa14549279a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_alg
import Theorems.Thm_PI_WADVR_Sm_pow
import Theorems.Thm_PI_WADVR_sm_natCast

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
theorem _root_.solution (hϖ : Irreducible ϖ) {p : ℕ} (hp : ¬ IsUnit (p : W)) {y x : Q} {N : ℕ}
    {c : W} (h : y = x + (p : Q) ^ N * algebraMap W Q c) : Sm Q ϖ N (y - x) := by
  have h1 := ((sm_natCast (Q := Q) hϖ hp).pow hϖ N).mul hϖ (Sm.alg c)
  rw [h, add_sub_cancel_left]
  simpa using h1
end PI.WADVR
