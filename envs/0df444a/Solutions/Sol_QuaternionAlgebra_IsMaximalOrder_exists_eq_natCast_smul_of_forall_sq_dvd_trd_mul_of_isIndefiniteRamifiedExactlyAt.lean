-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1c64984f-7854-55ce-9cf7-d5566da587f4

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

namespace B16R

open QuaternionAlgebra

variable {a b : ℚ}

theorem trd_add' (x y : ℍ[ℚ, a, b]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, trd_mk]
  ring

theorem trd_zero' : trd (0 : ℍ[ℚ, a, b]) = 0 := by
  simp [trd]

theorem trd_one' : trd (1 : ℍ[ℚ, a, b]) = 2 := by
  simp [trd]

theorem trd_smul' (c : ℚ) (x : ℍ[ℚ, a, b]) : trd (c • x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, trd_mk, smul_eq_mul]
  ring

theorem trd_zsmul' (n : ℤ) (x : ℍ[ℚ, a, b]) : trd (n • x) = (n : ℚ) * trd x := by
  rw [← Int.cast_smul_eq_zsmul ℚ, trd_smul']

theorem trd_mul_comm' (x y : ℍ[ℚ, a, b]) : trd (x * y) = trd (y * x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, trd_mk]
  ring

theorem trd_coe_mul' (c : ℚ) (x : ℍ[ℚ, a, b]) : trd ((c : ℍ[ℚ, a, b]) * x) = c * trd x := by
  rw [QuaternionAlgebra.coe_mul_eq_smul, trd_smul']

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

end B16R

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    ∀ l ∈ Λ, (∀ p ∈ Λ, (∃ n : ℤ, nrd p = (r : ℚ) * n) → ∃ t : ℤ, trd (l * p) = ((r : ℚ) ^ 2) * t) →
      ∃ l' ∈ Λ, l = (r : ℤ) • l' := by
  classical
  intro l hl hlp
  have hO : IsOrder Λ := hΛ.1
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hram := QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
    hB Λ hΛ r hr
  have hrad := QuaternionAlgebra.IsMaximalOrder.dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
    hB Λ hΛ r hr
  obtain ⟨π, hπ, hnπ, -, -, hgen⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr

  have h1 : ∃ n : ℤ, nrd l = (r : ℚ) * n := by
    refine hrad l hl (fun z hz => ?_)
    obtain ⟨t, ht⟩ := hlp ((r : ℤ) • z) (Λ.smul_mem _ hz) (hram.1.2.1 z hz)
    rw [mul_smul_comm, B16R.trd_zsmul'] at ht
    push_cast at ht
    refine ⟨t, mul_left_cancel₀ hr0 ?_⟩
    rw [ht]; ring
  obtain ⟨l₁, hl₁, rfl⟩ := (hgen l hl).1 h1

  have hsπ : star π ∈ Λ := by
    obtain ⟨⟨k, n, hk, -⟩, -⟩ := hO.exists_int_trd_eq_and_nrd_eq hπ
    have e : star π = (k : ℤ) • (1 : ℍ[ℚ, a, b]) - π := by
      have h := add_star_eq_coe_trd π
      rw [hk] at h
      have e2 : (((k : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (k : ℤ) • (1 : ℍ[ℚ, a, b]) := by
        rw [zsmul_eq_mul, mul_one]; norm_cast
      rw [e2] at h
      rw [← h]; abel
    rw [e]
    exact Λ.sub_mem (Λ.smul_mem _ hO.one_mem) hπ

  obtain ⟨e, he, hee⟩ : ∃ e : ℤ, nrd π = (r : ℚ) * e ∧ e * e = 1 := by
    rcases hnπ with h | h
    · exact ⟨1, by rw [h]; simp, by norm_num⟩
    · exact ⟨-1, by rw [h]; simp, by norm_num⟩

  have h2 : ∃ n : ℤ, nrd l₁ = (r : ℚ) * n := by
    refine hrad l₁ hl₁ (fun z hz => ?_)
    have hp : star π * z ∈ Λ := hO.mul_mem hsπ hz
    have hpn : ∃ n : ℤ, nrd (star π * z) = (r : ℚ) * n := by
      obtain ⟨⟨k, m, -, hm⟩, -⟩ := hO.exists_int_trd_eq_and_nrd_eq hz
      exact ⟨e * m, by rw [B16R.nrd_mul', nrd_star, he, hm]; push_cast; ring⟩
    obtain ⟨t, ht⟩ := hlp _ hp hpn
    have e1 : l₁ * π * (star π * z) = ((nrd π : ℚ) : ℍ[ℚ, a, b]) * (l₁ * z) := by
      rw [mul_assoc, ← mul_assoc π, mul_star_eq_coe_nrd, QuaternionAlgebra.coe_mul_eq_smul,
        mul_smul_comm, ← QuaternionAlgebra.coe_mul_eq_smul]
    rw [e1, B16R.trd_coe_mul', he] at ht
    have hee' : ((e : ℤ) : ℚ) * e = 1 := by exact_mod_cast hee
    have h3 : (e : ℚ) * trd (l₁ * z) = (r : ℚ) * t := by
      refine mul_left_cancel₀ hr0 ?_
      rw [← mul_assoc, ht]; ring
    refine ⟨e * t, ?_⟩
    calc trd (l₁ * z) = ((e : ℤ) : ℚ) * e * trd (l₁ * z) := by rw [hee', one_mul]
      _ = (e : ℚ) * ((r : ℚ) * t) := by rw [mul_assoc, h3]
      _ = (r : ℚ) * ((e * t : ℤ) : ℚ) := by push_cast; ring

  obtain ⟨y, hy, hyeq⟩ := hram.1.2.2.2.2 l₁ hl₁ π hπ h2 ⟨e, he⟩
  exact ⟨y, hy, hyeq⟩

end S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt (solution)
