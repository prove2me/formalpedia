-- Prove2me | solution 1 for PI.LocalEndW.valOfInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:44.024224+00:00
-- url     : https://prove2.me/submissions/5686e173-53fe-4130-97c8-f9ff8814138b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
import Theorems.Thm_PI_LocalEndW_exists_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW
namespace PI.LocalEndW
theorem _root_.solution : ValOfInt := by
  intro hI F _ _ v τ x
  obtain ⟨N, hNpos, m, hm, hNv, -⟩ := exists_N v
  have h1 : ∀ y : v.adicCompletion F, Valued.v y = 1 → Valued.v (τ y) = 1 := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have ht : Valued.v (τ y) ≠ 0 := by simp [hy0]
    apply le_antisymm (hI F v τ y hy.le)
    have h2 := hI F v τ y⁻¹ (by rw [map_inv₀, hy, inv_one])
    rw [map_inv₀, map_inv₀] at h2
    calc (1 : ℤᵐ⁰) = Valued.v (τ y) * (Valued.v (τ y))⁻¹ := (mul_inv_cancel₀ ht).symm
      _ ≤ Valued.v (τ y) * 1 := by gcongr
      _ = _ := mul_one _
  by_cases hx : x = 0
  · simp [hx]
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  have htx0 : Valued.v (τ x) ≠ 0 := by simp [hx]
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v x = exp a := ⟨_, (exp_log hx0).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, Valued.v (τ x) = exp b := ⟨_, (exp_log htx0).symm⟩
  have hy : Valued.v (x ^ m * (N : v.adicCompletion F) ^ a) = 1 := by
    rw [map_mul, map_pow, map_zpow₀, ha, hNv, ← exp_nsmul, ← exp_zsmul, ← exp_add, ← exp_zero]
    congr 1; simp; ring
  have hτy := h1 _ hy
  rw [map_mul, map_pow, map_zpow₀, map_natCast, map_mul, map_pow, map_zpow₀, hb, hNv, ← exp_nsmul,
    ← exp_zsmul, ← exp_add, ← exp_zero, exp_inj] at hτy
  simp only [nsmul_eq_mul, smul_eq_mul] at hτy
  have hmb : (m : ℤ) * (b - a) = 0 := by linarith
  rcases mul_eq_zero.1 hmb with h | h
  · omega
  · rw [ha, hb]; congr 1; linarith
end PI.LocalEndW
