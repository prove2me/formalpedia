-- Prove2me | solution 1 for PI.WADVR.big_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:51.122491+00:00
-- url     : https://prove2.me/submissions/844f07bc-5b51-4abc-b642-ce260b7a052e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_pow
import Theorems.Thm_PI_WADVR_one_add_of_sm

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
theorem _root_.solution (hϖ : Irreducible ϖ) {q : Q} (h0 : q ≠ 0) (h : Sm Q ϖ 1 q⁻¹) {r : ℕ}
    (hr : 1 ≤ r) : 1 + q ^ r ≠ 0 ∧ Sm Q ϖ r (1 + q ^ r)⁻¹ := by
  have ht : Sm Q ϖ r (q⁻¹ ^ r) := by simpa using h.pow hϖ r
  have ht1 : Sm Q ϖ 1 (q⁻¹ ^ r) := ht.mono hϖ (by exact_mod_cast hr)
  obtain ⟨h1, h2⟩ := one_add_of_sm hϖ ht1
  have hid : 1 + q ^ r = q ^ r * (1 + q⁻¹ ^ r) := by
    rw [mul_add, mul_one, ← mul_pow, mul_inv_cancel₀ h0, one_pow]; ring
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ h0
  refine ⟨hid ▸ mul_ne_zero hqr h1, ?_⟩
  have := ht.mul hϖ h2
  rw [add_zero] at this
  convert this using 1
  rw [hid, mul_inv, inv_pow]
end PI.WADVR
