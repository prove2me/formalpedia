-- Prove2me | solution 1 for ValuationSubring.mulArchimedean_valueGroup_iff_forall_exists_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d985ae73-3282-5ddc-8f8f-1eedcde5dad5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_mulArchimedean_valueGroup_iff_forall_exists_pow_le

set_option autoImplicit false

theorem solution {L : Type*} [Field L] (A : ValuationSubring L) :
    MulArchimedean A.ValueGroup ↔
      (∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
        ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x) := by
  constructor
  · intro hA x hx y hy
    by_cases hy0 : (y : L) = 0
    · exact ⟨1, by simp [hy0]⟩
    · have hvy : A.valuation (y : L) < 1 := (A.valuation_lt_one_iff y).mp hy
      have hvy0 : 0 < A.valuation (y : L) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
      have hvx0 : 0 < A.valuation x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx)
      have h1 : 1 < (A.valuation (y : L))⁻¹ := (one_lt_inv₀ hvy0).mpr hvy
      obtain ⟨n, hn⟩ := MulArchimedean.arch (A.valuation x)⁻¹ h1
      refine ⟨n, ?_⟩
      rw [map_pow]
      rw [inv_pow, inv_le_inv₀ hvx0 (pow_pos hvy0 n)] at hn
      exact hn
  · intro h
    constructor
    intro X Y hY
    by_cases hX : X = 0
    · exact ⟨0, by simp [hX]⟩
    obtain ⟨x, rfl⟩ := A.valuation_surjective X
    obtain ⟨z, rfl⟩ := A.valuation_surjective Y
    have hx : x ≠ 0 := fun h0 => hX (by rw [h0, map_zero])
    have hz0 : 0 < A.valuation z := lt_trans zero_lt_one hY
    have hz : z ≠ 0 := (Valuation.ne_zero_iff _).mp hz0.ne'
    have hvx0 : 0 < A.valuation x := zero_lt_iff.mpr hX
    have hzinv : A.valuation z⁻¹ < 1 := by
      rw [map_inv₀]
      exact (inv_lt_one₀ hz0).mpr hY
    obtain ⟨hzA, hzm⟩ := A.mem_nonunits_iff_exists_mem_maximalIdeal.mp (A.mem_nonunits_iff.mpr hzinv)
    obtain ⟨n, hn⟩ := h x⁻¹ (inv_ne_zero hx) ⟨z⁻¹, hzA⟩ hzm
    refine ⟨n, ?_⟩
    have hn' : ((A.valuation z) ^ n)⁻¹ ≤ (A.valuation x)⁻¹ := by
      simpa [map_pow, map_inv₀, inv_pow] using hn
    exact (inv_le_inv₀ (pow_pos hz0 n) hvx0).mp hn'

end S_ValuationSubring_mulArchimedean_valueGroup_iff_forall_exists_pow_le
end P2MW
export P2MW.S_ValuationSubring_mulArchimedean_valueGroup_iff_forall_exists_pow_le (solution)
