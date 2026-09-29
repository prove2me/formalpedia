-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/635b7d4d-161a-5697-9457-f2dfeb6dce67

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

namespace PrinLine12

variable {a b : ℚ}

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨⟨t, n, ht, -⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hx
  have h : star x = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - x := by
    have h2 := add_star_eq_coe_trd x
    rw [ht] at h2
    have h3 : star x = ((t : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← h2]; abel
    rw [h3, zsmul_eq_mul, mul_one]
    norm_cast
  rw [h]
  exact Λ.sub_mem (Λ.smul_mem _ hΛ.one_mem) hx

theorem nrd_intCast_smul (n : ℤ) (y : ℍ[ℚ, a, b]) : nrd ((n : ℤ) • y) = (n : ℚ) ^ 2 * nrd y := by
  have : (n : ℤ) • y = ((n : ℚ) : ℍ[ℚ, a, b]) * y := by
    rw [coe_mul_eq_smul]; norm_cast
  rw [this, QuaternionAlgebra.nrd_mul, nrd_coe]

theorem smul_star_mul_self {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ)
    (N : ℤ) (hN : (N : ℚ) = nrd x) (hN1 : N * N = 1) :
    ((N : ℤ) • star x) * x = 1 ∧ (N : ℤ) • star x ∈ Λ := by
  refine ⟨?_, Λ.smul_mem _ (star_mem hΛ hx)⟩
  rw [smul_mul_assoc, star_mul_eq_coe_nrd, ← hN, zsmul_eq_mul]
  norm_cast
  rw [hN1]; norm_cast

end PrinLine12

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J)
    (hidx : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ s ∈ Λ, (nrd s = (ℓ : ℚ) ∨ nrd s = -(ℓ : ℚ)) ∧ ∀ x : ℍ[ℚ, a, b], x ∈ J ↔ ∃ m ∈ Λ, x = m * s := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hJfg : J.FG := by
    haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hO.fg
    have h1 : (J.comap Λ.subtype).FG := IsNoetherian.noetherian _
    have h2 : (J.comap Λ.subtype).map Λ.subtype = J := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hJΛ]
    rw [← h2]; exact h1.map _
  have hJspan : Submodule.span ℚ (J : Set ℍ[ℚ, a, b]) = ⊤ := by
    apply top_le_iff.1
    rw [← hO.spanTop]
    apply Submodule.span_le.2
    intro x hx
    have h1 : (ℓ : ℤ) • x ∈ Submodule.span ℚ (J : Set ℍ[ℚ, a, b]) := Submodule.subset_span (hℓJ x hx)
    have h2 : x = (ℓ : ℚ)⁻¹ • ((ℓ : ℤ) • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; rw [inv_mul_cancel₀ hℓ0, one_smul]
    rw [h2]; exact Submodule.smul_mem _ _ h1
  obtain ⟨x₀, hx0, hJ⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ J hJfg hJspan hleft
  have hx₀J : x₀ ∈ J := (hJ x₀).2 ⟨1, hO.one_mem, one_mul _⟩
  have hx₀Λ : x₀ ∈ Λ := hJΛ hx₀J

  obtain ⟨m, hm, hmx⟩ := (hJ _).1 (hℓJ 1 hO.one_mem)
  obtain ⟨⟨M, N', hM', hM⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hm
  obtain ⟨⟨T, Nn, hT, hN⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hx₀Λ
  clear hM' hT
  have hMN : N' * Nn = (ℓ : ℤ) ^ 2 := by
    have h := congrArg nrd hmx
    rw [QuaternionAlgebra.nrd_mul, PrinLine12.nrd_intCast_smul, nrd_one, hM, hN, mul_one] at h
    exact_mod_cast h
  have hdvd : Nn.natAbs ∣ ℓ ^ 2 := by
    refine ⟨N'.natAbs, ?_⟩
    have := congrArg Int.natAbs hMN
    rw [Int.natAbs_mul, Int.natAbs_pow] at this
    simpa [mul_comm] using this.symm
  obtain ⟨k, hk, hkN⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
  interval_cases k
  ·
    exfalso
    rw [pow_zero] at hkN
    have hN1 : Nn * Nn = 1 := by
      rcases Int.natAbs_eq_iff.1 hkN with h | h <;> simp [h]
    obtain ⟨hinv, hmem⟩ := PrinLine12.smul_star_mul_self hO hx₀Λ Nn (by exact_mod_cast hN.symm) hN1
    have hΛJ : Λ ≤ J := by
      intro y hy
      exact (hJ y).2 ⟨y * ((Nn : ℤ) • star x₀), hO.mul_mem hy hmem, by rw [mul_assoc, hinv, mul_one]⟩
    have h1 : J.toAddSubgroup.relIndex Λ.toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.2 (fun y hy => hΛJ hy)
    rw [h1] at hidx
    have : (1 : ℕ) < ℓ ^ 2 := Nat.one_lt_pow (by norm_num) hℓ.one_lt
    exact (ne_of_lt this) hidx
  ·
    rw [pow_one] at hkN
    refine ⟨x₀, hx₀Λ, ?_, fun x => (hJ x).trans ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩⟩
    have hNq : nrd x₀ = (Nn : ℚ) := hN
    rcases Int.natAbs_eq_iff.1 hkN with h | h
    · left; rw [hNq, h]; push_cast; rfl
    · right; rw [hNq, h]; push_cast; rfl
  ·
    exfalso
    have hM1 : N' * N' = 1 := by
      have h5 : N'.natAbs * ℓ ^ 2 = 1 * ℓ ^ 2 := by
        have := congrArg Int.natAbs hMN
        rw [Int.natAbs_mul, hkN, Int.natAbs_pow] at this
        simpa using this
      have h6 : N'.natAbs = 1 := Nat.eq_of_mul_eq_mul_right (pow_pos hℓ.pos 2) h5
      rcases Int.natAbs_eq_iff.1 h6 with h | h <;> simp [h]
    obtain ⟨hinv, hmem⟩ := PrinLine12.smul_star_mul_self hO hm N' (by exact_mod_cast hM.symm) hM1

    have hx₀eq : x₀ = (ℓ : ℤ) • (((N' : ℤ) • star m) * 1) := by
      have := congrArg (fun z => ((N' : ℤ) • star m) * z) hmx
      try simp only at this
      rw [← mul_assoc, hinv, one_mul] at this
      rw [this, mul_smul_comm]
    let ℓΛ : Submodule ℤ ℍ[ℚ, a, b] := Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))
    have hJle : J ≤ ℓΛ := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := (hJ y).1 hy
      apply Submodule.subset_span
      refine ⟨z * (((N' : ℤ) • star m) * 1), hO.mul_mem hz (by rw [mul_one]; exact hmem), ?_⟩
      show (ℓ : ℤ) • (z * ((N' : ℤ) • star m * 1)) = z * x₀
      rw [hx₀eq, mul_smul_comm]
    have hleJ : ℓΛ ≤ J := Submodule.span_le.2 (by rintro _ ⟨y, hy, rfl⟩; exact hℓJ y hy)
    have hJeq : J = ℓΛ := le_antisymm hJle hleJ
    have h4 : ℓΛ.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 :=
      QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO ℓ hℓ.pos
    rw [← hJeq, hidx] at h4
    have : ℓ ^ 2 < ℓ ^ 4 := Nat.pow_lt_pow_right hℓ.one_lt (by norm_num)
    exact (ne_of_lt this) h4

end S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt (solution)
