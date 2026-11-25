-- Prove2me | solution 1 for PI.WA.g_B_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:11.630743+00:00
-- url     : https://prove2.me/submissions/6b88835b-b186-4b43-9327-8907659dd384

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
import Theorems.Thm_PI_WADVR_Sm_add
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_one
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
theorem _root_.solution (hϖ : Irreducible ϖ) {q Y : Q} (hq : q ≠ 0) (hqs : Sm Q ϖ 1 q⁻¹) (hY0 : Y ≠ 0)
    (hY : Sm Q ϖ 1 Y⁻¹) {r : ℕ} (hr : 1 ≤ r) :
    1 + q ^ r ≠ 0 ∧ Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ := by
  have ht : Sm Q ϖ 1 ((q⁻¹) ^ r) := (Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)
  obtain ⟨ht0, -⟩ := one_add_of_sm hϖ ht
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ hq
  have h1 : 1 + q ^ r ≠ 0 := by
    intro h
    apply ht0
    have e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r) := by
      rw [inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]
    rw [e, h, mul_zero]
  refine ⟨h1, ?_⟩
  have e : (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ = (1 + (q⁻¹) ^ r) * Y⁻¹ := by
    rw [inv_pow]
    field_simp
    ring
  rw [e]
  have h2 : Sm Q ϖ 0 (1 + (q⁻¹) ^ r) := Sm.add Sm.one (ht.mono hϖ (by norm_num))
  have h3 := h2.mul hϖ hY
  simpa using h3
end PI.WA
