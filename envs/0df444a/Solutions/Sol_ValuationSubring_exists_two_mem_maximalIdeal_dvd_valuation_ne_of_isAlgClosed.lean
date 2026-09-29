-- Prove2me | solution 1 for ValuationSubring.exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/55b85ac2-085b-58ee-a9e7-abebb5d60fc4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed

set_option autoImplicit false

open IsLocalRing

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (m : ↥A) (hm : m ∈ maximalIdeal ↥A) (hm0 : (m : L) ≠ 0) :
    ∃ c₁ c₂ : ↥A, c₁ ∈ maximalIdeal ↥A ∧ c₂ ∈ maximalIdeal ↥A ∧ (c₁ : L) ≠ 0 ∧ (c₂ : L) ≠ 0 ∧
      (∃ m₁ ∈ maximalIdeal ↥A, (m : L) = c₁ * m₁) ∧ (∃ m₂ ∈ maximalIdeal ↥A, (m : L) = c₂ * m₂) ∧
      A.valuation (c₁ : L) ≠ A.valuation (c₂ : L) := by
  obtain ⟨r₂, hr₂⟩ := IsAlgClosed.exists_pow_nat_eq (m : L) (by norm_num : 0 < 2)
  obtain ⟨r₃, hr₃⟩ := IsAlgClosed.exists_pow_nat_eq (m : L) (by norm_num : 0 < 3)
  set v := A.valuation with hv
  have hvm1 : v (m : L) < 1 := (A.valuation_lt_one_iff m).mp hm
  have hvm0 : v (m : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hm0
  have hv2 : v r₂ ^ 2 = v (m : L) := by rw [← map_pow, hr₂]
  have hv3 : v r₃ ^ 3 = v (m : L) := by rw [← map_pow, hr₃]
  have hr₂0 : r₂ ≠ 0 := by rintro rfl; apply hm0; rw [← hr₂]; simp
  have hr₃0 : r₃ ≠ 0 := by rintro rfl; apply hm0; rw [← hr₃]; simp

  have hlt₂ : v r₂ < 1 := by
    by_contra h
    have h1 : 1 ≤ v r₂ := not_lt.mp h
    have : 1 ≤ v r₂ ^ 2 := one_le_pow₀ h1
    exact absurd (hv2 ▸ this) (not_le.mpr hvm1)
  have hlt₃ : v r₃ < 1 := by
    by_contra h
    have h1 : 1 ≤ v r₃ := not_lt.mp h
    have : 1 ≤ v r₃ ^ 3 := one_le_pow₀ h1
    exact absurd (hv3 ▸ this) (not_le.mpr hvm1)
  have hmem₂ : r₂ ∈ A := (A.valuation_le_one_iff r₂).mp hlt₂.le
  have hmem₃ : r₃ ∈ A := (A.valuation_le_one_iff r₃).mp hlt₃.le
  have hmax₂ : (⟨r₂, hmem₂⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨r₂, hmem₂⟩).mpr hlt₂
  have hmax₃ : (⟨r₃, hmem₃⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨r₃, hmem₃⟩).mpr hlt₃
  have hsq₃ : (⟨r₃, hmem₃⟩ * ⟨r₃, hmem₃⟩ : ↥A) ∈ maximalIdeal ↥A := Ideal.mul_mem_left _ _ hmax₃
  refine ⟨⟨r₂, hmem₂⟩, ⟨r₃, hmem₃⟩, hmax₂, hmax₃, hr₂0, hr₃0, ⟨⟨r₂, hmem₂⟩, hmax₂, ?_⟩,
    ⟨⟨r₃, hmem₃⟩ * ⟨r₃, hmem₃⟩, hsq₃, ?_⟩, ?_⟩
  · show (m : L) = r₂ * r₂
    rw [← hr₂]; ring
  · show (m : L) = r₃ * (r₃ * r₃)
    rw [← hr₃]; ring
  ·
    intro heq
    change v r₂ = v r₃ at heq
    have hne0 : v r₂ ≠ 0 := (Valuation.ne_zero_iff _).mpr hr₂0
    have h23 : v r₂ ^ 2 = v r₂ ^ 3 := by rw [hv2, ← hv3, heq]
    have h2ne : v r₂ ^ 2 ≠ 0 := pow_ne_zero _ hne0
    have : v r₂ = 1 := by
      have h : v r₂ ^ 2 * v r₂ = v r₂ ^ 2 * 1 := by rw [mul_one, ← pow_succ, ← h23]
      exact mul_left_cancel₀ h2ne h
    exact absurd this (ne_of_lt hlt₂)

end S_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed
end P2MW
export P2MW.S_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed (solution)
