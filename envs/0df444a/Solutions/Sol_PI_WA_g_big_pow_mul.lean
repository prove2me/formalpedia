-- Prove2me | solution 1 for PI.WA.g_big_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:41.487684+00:00
-- url     : https://prove2.me/submissions/f9ac6b9b-af2b-41ae-94e8-cbbf37503ae5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WA
open PI.WADVR
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}
namespace PI.WA
theorem _root_.solution (hϖ : Irreducible ϖ) {q Y : Q} (hqs : Sm Q ϖ 1 q⁻¹) (hY : Sm Q ϖ 1 Y⁻¹)
    (r : ℕ) : Sm Q ϖ 1 (q ^ r * Y)⁻¹ := by
  have h1 := (Sm.pow hϖ hqs r).mul hϖ hY
  rw [mul_inv, ← inv_pow]
  exact h1.mono hϖ (by push_cast; omega)
end PI.WA
