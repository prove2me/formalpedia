-- Prove2me | solution 1 for PI.WA.g_B_bigj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:46.036156+00:00
-- url     : https://prove2.me/submissions/6839f40f-4620-4fba-955f-d7372518873a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_mul
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
open PI PI.WA
open PI.WADVR
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}
namespace PI.WA
theorem _root_.solution (hϖ : Irreducible ϖ) {q Y : Q} (hq : q ≠ 0) (hqs : Sm Q ϖ 1 q⁻¹)
    (hY : Sm Q ϖ 1 Y) {r : ℕ} (hr : 1 ≤ r) : Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y) := by
  have ht : Sm Q ϖ 1 ((q⁻¹) ^ r) := (Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)
  obtain ⟨ht0, hinv⟩ := one_add_of_sm hϖ ht
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ hq
  have h1 : 1 + q ^ r ≠ 0 := by
    intro h
    apply ht0
    have e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r) := by
      rw [inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]
    rw [e, h, mul_zero]
  have e : q ^ r * (1 + q ^ r)⁻¹ = (1 + (q⁻¹) ^ r)⁻¹ := by
    rw [inv_pow, eq_comm, inv_eq_iff_eq_inv, mul_inv, inv_inv, mul_add, inv_mul_cancel₀ hqr, mul_one,
      add_comm]
  rw [e]
  simpa using hinv.mul hϖ hY
end PI.WA
