-- Prove2me | solution 1 for PI.Mk.card_dvd_sum_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:48.503011+00:00
-- url     : https://prove2.me/submissions/59f9bf5e-6372-428d-a79f-c5505aabe13f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum
import Theorems.Thm_PI_Mk_trace_idem_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Matrix Finset
namespace PI.Mk
theorem _root_.solution {H : Type*} [Group H] [Fintype H] {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : H → Matrix n n ℤ) (hρ : ∀ a b, ρ (a * b) = ρ a * ρ b) :
    (Fintype.card H : ℤ) ∣ ∑ h : H, (ρ h).trace := by
  classical
  let M : H → Matrix n n ℚ := fun h => (ρ h).map (Int.castRingHom ℚ)
  have hM : ∀ a b, M (a * b) = M a * M b := fun a b => by
    simp only [M, hρ, Matrix.map_mul]
  have hc : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : ∀ a, M a * ∑ h, M h = ∑ h, M h := fun a => by
    rw [Finset.mul_sum]
    simp_rw [← hM]
    exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)
  have hE : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) * ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) =
      (Fintype.card H : ℚ)⁻¹ • ∑ h, M h := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul]
    simp_rw [hsum]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul,
      mul_assoc, inv_mul_cancel₀ hc, mul_one]
  obtain ⟨r, hr⟩ := trace_idem_nat _ hE
  have htr : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h).trace = (Fintype.card H : ℚ)⁻¹ * ∑ h, ((ρ h).trace : ℚ) := by
    rw [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [M, Matrix.trace]
  rw [htr, inv_mul_eq_iff_eq_mul₀ hc] at hr
  refine ⟨(r : ℤ), ?_⟩
  have h2 : ((∑ h, (ρ h).trace : ℤ) : ℚ) = (((Fintype.card H : ℤ) * (r : ℤ) : ℤ) : ℚ) := by
    push_cast
    exact hr
  exact_mod_cast h2
end PI.Mk
