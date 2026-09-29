-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/defa3f3d-99ae-527b-bb1f-5225bd5d792a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
open scoped Quaternion
open QuaternionAlgebra

namespace RamIdeal2

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

end RamIdeal2

open RamIdeal2 in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :

    ((∀ m ∈ Λ, ∀ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → ∃ n : ℤ, nrd (m * x) = (r : ℚ) * n) ∧
      (∀ y ∈ Λ, ∃ n : ℤ, nrd ((r : ℤ) • y) = (r : ℚ) * n) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) ∧ ¬ ∃ y ∈ Λ, x = (r : ℤ) • y) ∧
      (∃ x ∈ Λ, ¬ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∧

      (∀ x ∈ Λ, ∀ x' ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → (∃ n : ℤ, nrd x' = (r : ℚ) * n) →
        ∃ y ∈ Λ, x * x' = (r : ℤ) • y)) ∧

    ∀ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ → (∀ y ∈ Λ, (r : ℤ) • y ∈ J) → (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) →
      (∀ x, x ∈ J ↔ ∃ y ∈ Λ, x = (r : ℤ) • y) ∨
      (∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∨
      J = Λ := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by
    rcases hr with h1 | h1 <;> rw [h1] <;> exact Fact.out
  haveI : Fact r.Prime := ⟨hrp⟩
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hint : ∀ x ∈ Λ, ∃ n : ℤ, nrd x = (n : ℚ) := fun x hx => by
    obtain ⟨⟨n, hn⟩, -⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
    exact ⟨n, hn.symm⟩

  have hsmul : ∀ y : ℍ[ℚ, a, b], (r : ℤ) • y = ((r : ℚ) : ℍ[ℚ, a, b]) * y := fun y => by
    rw [coe_mul_eq_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rintro m hm x hx ⟨n, hn⟩
    obtain ⟨k, hk⟩ := hint m hm
    exact ⟨k * n, by rw [QuaternionAlgebra.nrd_mul, hk, hn]; push_cast; ring⟩
  ·
    intro y hy
    obtain ⟨k, hk⟩ := hint y hy
    refine ⟨(r : ℤ) * k, ?_⟩
    rw [hsmul, QuaternionAlgebra.nrd_mul, nrd_coe, hk]; push_cast; ring
  ·
    obtain ⟨h, hh, hne, n, hn, ⟨k, hk⟩⟩ := IsOrder.exists_mem_dvd_nrd_forall_ne_smul hO r
    refine ⟨h, hh, ⟨k, ?_⟩, ?_⟩
    · rw [← hn, hk]; push_cast; ring
    · rintro ⟨y, hy, hhy⟩
      exact hne y hy hhy
  ·
    refine ⟨1, hO.one_mem, ?_⟩
    rintro ⟨n, hn⟩
    rw [nrd_one] at hn
    have h1 : (r : ℤ) * n = 1 := by exact_mod_cast hn.symm
    have hdvd : (r : ℤ) ∣ 1 := ⟨n, h1.symm⟩
    have : r ∣ 1 := by exact_mod_cast Int.natCast_dvd_natCast.mp (by simpa using hdvd)
    exact hrp.one_lt.ne' (Nat.dvd_one.mp this)
  ·
    exact QuaternionAlgebra.IsMaximalOrder.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr

  intro J hJ hrJ hmulJ
  by_cases hA : ∃ x ∈ J, ¬ ∃ n : ℤ, nrd x = (r : ℚ) * n
  ·
    right; right
    obtain ⟨x, hxJ, hxn⟩ := hA
    have hxΛ : x ∈ Λ := hJ hxJ
    obtain ⟨n, hn⟩ := hint x hxΛ
    have hndvd : ¬ (r : ℤ) ∣ n := by
      rintro ⟨k, hk⟩
      exact hxn ⟨k, by rw [hn, hk]; push_cast; ring⟩
    apply le_antisymm hJ
    intro y hy
    have h1 : n • y ∈ J := by
      have hmem : y * star x * x ∈ J := hmulJ (y * star x) (hO.mul_mem hy (RamIdeal2.star_mem_of_mem hO hxΛ)) x hxJ
      rw [mul_assoc, star_mul_eq_coe_nrd, mul_coe_eq_smul, hn, Int.cast_smul_eq_zsmul] at hmem
      exact hmem
    exact RamIdeal2.mem_of_smul_mem_of_not_dvd hrp J hndvd h1 (hrJ y hy)
  · have hA' : ∀ x ∈ J, ∃ n : ℤ, nrd x = (r : ℚ) * n := by
      intro x hx
      by_contra hno
      exact hA ⟨x, hx, hno⟩
    by_cases hB' : ∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (r : ℤ) • y
    ·
      right; left
      obtain ⟨x, hxJ, hxR⟩ := hB'
      have hxΛ : x ∈ Λ := hJ hxJ
      obtain ⟨m, hm⟩ := hA' x hxJ
      have hmdvd : ¬ (r : ℤ) ∣ m := by
        rintro ⟨k, hk⟩
        apply hxR
        exact RamIdeal2.exists_eq_smul_of_nrd_eq_sq_mul hB hΛ hr hxΛ k (by rw [hm, hk]; push_cast; ring)
      intro z
      constructor
      · intro hz; exact ⟨hJ hz, hA' z hz⟩
      · rintro ⟨hzΛ, n, hzn⟩
        have hzs : z * star x ∈ Λ := hO.mul_mem hzΛ (RamIdeal2.star_mem_of_mem hO hxΛ)
        obtain ⟨w, hw, hzw⟩ := RamIdeal2.exists_eq_smul_of_nrd_eq_sq_mul hB hΛ hr hzs (n * m)
          (by rw [QuaternionAlgebra.nrd_mul, nrd_star, hzn, hm]; push_cast; ring)

        have e1 : z * star x * x = ((r : ℚ) * m) • z := by
          rw [mul_assoc, star_mul_eq_coe_nrd, mul_coe_eq_smul, hm]
        have e2 : z * star x * x = (r : ℚ) • (w * x) := by
          rw [hzw, hsmul, mul_assoc, coe_mul_eq_smul]
        have e3 : (m : ℤ) • z = w * x := by
          have h12 : (r : ℚ) • ((m : ℚ) • z) = (r : ℚ) • (w * x) := by rw [smul_smul, ← e1, e2]
          have := smul_right_injective ℍ[ℚ, a, b] hr0 h12
          rw [← Int.cast_smul_eq_zsmul ℚ]
          exact this
        have h1 : (m : ℤ) • z ∈ J := by rw [e3]; exact hmulJ w hw x hxJ
        exact RamIdeal2.mem_of_smul_mem_of_not_dvd hrp J hmdvd h1 (hrJ z hzΛ)
    ·
      left
      have hC : ∀ x ∈ J, ∃ y ∈ Λ, x = (r : ℤ) • y := by
        intro x hx
        by_contra hno
        exact hB' ⟨x, hx, hno⟩
      intro z
      exact ⟨hC z, fun ⟨y, hy, hzy⟩ => hzy ▸ hrJ y hy⟩

end S_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq (solution)
