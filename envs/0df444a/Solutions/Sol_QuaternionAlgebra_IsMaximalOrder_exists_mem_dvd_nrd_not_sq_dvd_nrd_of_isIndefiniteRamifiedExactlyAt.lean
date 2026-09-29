-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1dfa68c3-3161-505a-8c1c-f64b708858cf

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
open scoped Quaternion
open QuaternionAlgebra

namespace NormRKit

variable {a b : ℚ}

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨-, t, ht⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
  have hs : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by
    rw [← add_star_eq_coe_trd, add_sub_cancel_left]
  have hc : ((trd x : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, ← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [hs, hc]
  exact Λ.sub_mem (Λ.smul_mem _ hO.one_mem) hx

theorem nrd_add_coe (x : ℍ[ℚ, a, b]) (c : ℚ) : nrd (x + (c : ℍ[ℚ, a, b])) = nrd x + c * trd x + c ^ 2 := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  have hc : ((c : ℚ) : ℍ[ℚ, a, b]) = ⟨c, 0, 0, 0⟩ := rfl
  rw [hc, QuaternionAlgebra.mk_add_mk, nrd_mk, nrd_mk, trd_mk]
  ring

theorem mem_of_smul_mem_of_not_dvd {r : ℕ} (hrp : r.Prime) (J : Submodule ℤ ℍ[ℚ, a, b]) {z : ℍ[ℚ, a, b]} {m : ℤ}
    (hm : ¬ (r : ℤ) ∣ m) (h1 : m • z ∈ J) (h2 : (r : ℤ) • z ∈ J) : z ∈ J := by
  have hcop : IsCoprime (r : ℤ) m := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hrp)).mpr hm
  obtain ⟨u, w, huw⟩ := hcop
  have : z = u • ((r : ℤ) • z) + w • (m • z) := by
    rw [smul_smul, smul_smul, ← add_smul, huw, one_smul]
  rw [this]
  exact J.add_mem (J.smul_mem u h2) (J.smul_mem w h1)

section Ramified

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

theorem two_le_padicValRat_mul_mul {r : ℕ} (hrp : r.Prime) {K : ℤ} (hK : K ≠ 0) :
    haveI : Fact r.Prime := ⟨hrp⟩
    2 ≤ padicValRat r ((r : ℚ) * (r : ℚ) * (K : ℚ)) := by
  haveI : Fact r.Prime := ⟨hrp⟩
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hK0 : ((K : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hK
  rw [padicValRat.mul (mul_ne_zero hr0 hr0) hK0, padicValRat.mul hr0 hr0, padicValRat.self hrp.one_lt, padicValRat.of_int]
  have : (0 : ℤ) ≤ (padicValInt r K : ℤ) := by exact_mod_cast Nat.zero_le _
  omega

theorem coe_intCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ) (c : ℤ) : (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (c : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [this]
  exact Λ.smul_mem _ hO.one_mem

theorem exists_eq_smul_of_nrd_eq_zero (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {r : ℕ} (hr : r = q ∨ r = q')
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (hx0 : nrd x = 0) : ∃ y ∈ Λ, x = (r : ℤ) • y := by
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by
    rcases hr with h1 | h1 <;> rw [h1] <;> exact Fact.out
  have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  obtain ⟨-, t, ht⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
  have hex : ∃ k₀ : ℤ, k₀ ≠ 0 ∧ t + (r : ℤ) * r * k₀ ≠ 0 := by
    by_cases h : t + (r : ℤ) * r * 1 = 0
    · refine ⟨2, two_ne_zero, fun h2 => ?_⟩
      have hrr : (r : ℤ) * r = 0 := by linarith
      exact mul_ne_zero hrz hrz hrr
    · exact ⟨1, one_ne_zero, h⟩
  obtain ⟨k₀, hk₀, hne⟩ := hex
  set c : ℤ := (r : ℤ) * r * k₀ with hc
  have hx' : x + (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := Λ.add_mem hx (coe_intCast_mem hO c)
  have hnrd : nrd (x + (((c : ℤ) : ℚ) : ℍ[ℚ, a, b])) = (r : ℚ) * (r : ℚ) * (((k₀ * (t + c)) : ℤ) : ℚ) := by
    rw [nrd_add_coe, hx0, ← ht, hc]; push_cast; ring
  obtain ⟨y, hy, hxy⟩ := QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr hx'
    (Or.inr (by rw [hnrd]; exact two_le_padicValRat_mul_mul hrp (mul_ne_zero hk₀ hne)))
  refine ⟨y - (((r : ℤ) * k₀ : ℤ) : ℚ) • (1 : ℍ[ℚ, a, b]), Λ.sub_mem hy ?_, ?_⟩
  · rw [Int.cast_smul_eq_zsmul]; exact Λ.smul_mem _ hO.one_mem
  · have hcoe : (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (r : ℤ) • ((((r : ℤ) * k₀ : ℤ) : ℚ) • (1 : ℍ[ℚ, a, b])) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← coe_mul_eq_smul, mul_one]
      congr 1
      rw [hc]; push_cast; ring
    calc x = (x + (((c : ℤ) : ℚ) : ℍ[ℚ, a, b])) - (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by rw [add_sub_cancel_right]
      _ = (r : ℤ) • y - (r : ℤ) • ((((r : ℤ) * k₀ : ℤ) : ℚ) • (1 : ℍ[ℚ, a, b])) := by rw [← hxy, ← hcoe]
      _ = (r : ℤ) • (y - (((r : ℤ) * k₀ : ℤ) : ℚ) • (1 : ℍ[ℚ, a, b])) := by rw [smul_sub]

theorem exists_eq_smul_of_nrd_eq_sq_mul (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {r : ℕ} (hr : r = q ∨ r = q')
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (k : ℤ) (hk : nrd x = (r : ℚ) * (r : ℚ) * (k : ℚ)) :
    ∃ y ∈ Λ, x = (r : ℤ) • y := by
  have hrp : r.Prime := by
    rcases hr with h1 | h1 <;> rw [h1] <;> exact Fact.out
  by_cases hk0 : k = 0
  · exact exists_eq_smul_of_nrd_eq_zero hB hΛ hr hx (by rw [hk, hk0]; simp)
  · exact QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr hx (Or.inr (by rw [hk]; exact two_le_padicValRat_mul_mul hrp hk0))

end Ramified

end NormRKit

open NormRKit in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (r : ℕ) (hr : r = q ∨ r = q') :
    ∃ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) ∧ ¬ (∃ n : ℤ, nrd x = (r : ℚ) ^ 2 * n) := by
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by
    rcases hr with h1 | h1 <;> rw [h1] <;> exact Fact.out
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨x, hx, hne, n, hn, ⟨k, hk⟩⟩ := IsOrder.exists_mem_dvd_nrd_forall_ne_smul hO r
  refine ⟨x, hx, ⟨k, by rw [← hn, hk]; push_cast; ring⟩, ?_⟩
  rintro ⟨m, hm⟩
  obtain ⟨y, hy, hxy⟩ := NormRKit.exists_eq_smul_of_nrd_eq_sq_mul hB hΛ hr hx m (by rw [hm]; ring)
  exact hne y hy hxy

end S_QuaternionAlgebra_IsMaximalOrder_exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt (solution)
