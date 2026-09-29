-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f9f802c8-0e6a-59d2-92e7-a3cd84deb54e

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_nrd_eq_or_eq_neg_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
p2m_open "QuaternionAlgebra~nrd_mul"

namespace PrincGen

variable {a b : ℚ}

theorem nrd_mul (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  have h : (((nrd (x * y)) : ℚ) : ℍ[ℚ, a, b]) = ((nrd x * nrd y : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← mul_star_eq_coe_nrd, star_mul, mul_assoc, ← mul_assoc y, mul_star_eq_coe_nrd, coe_commutes, ← mul_assoc,
      mul_star_eq_coe_nrd, ← coe_mul]
  exact QuaternionAlgebra.coe_injective h

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem nrd_int (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : ∃ k : ℤ, nrd x = k := by
  obtain ⟨⟨k, hk⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hx
  exact ⟨k, hk.symm⟩

theorem intCast_mem (hΛ : IsOrder Λ) (z : ℤ) : (((z : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (((z : ℚ)) : ℍ[ℚ, a, b]) = z • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem z hΛ.one_mem

theorem star_mem (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨-, ⟨t, ht⟩⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hx
  have h : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [h, ← ht]
  exact Λ.sub_mem (intCast_mem hΛ t) hx

end PrincGen

open PrincGen in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    ∃ π : ℍ[ℚ, a, b], π ∈ Λ ∧ (nrd π = (r : ℚ) ∨ nrd π = -(r : ℚ)) ∧
      (∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π) ∧
      (∀ x ∈ Λ, ∃ y ∈ Λ, x * π = π * y) ∧
      (∀ m ∈ Λ, (∃ n : ℤ, nrd m = (r : ℚ) * n) ↔ ∃ l ∈ Λ, m = l * π) := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  obtain ⟨π, hπ, hnrd⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_nrd_eq_or_eq_neg_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr

  obtain ⟨n, hn, hnn⟩ : ∃ n : ℤ, nrd π = (r : ℚ) * n ∧ ((n : ℚ)) * n = 1 := by
    rcases hnrd with h | h
    · exact ⟨1, by rw [h]; simp, by norm_num⟩
    · exact ⟨-1, by rw [h]; simp, by norm_num⟩
  have hsπ : star π ∈ Λ := star_mem hO hπ
  have hr_ndvd_one : ∀ k : ℤ, (r : ℚ) * k ≠ 1 ∧ (r : ℚ) * k ≠ -1 := by
    intro k
    have key : ∀ z : ℤ, (r : ℤ) * k = z → z.natAbs = 1 → False := by
      intro z hz h1
      have h := congrArg Int.natAbs hz
      rw [Int.natAbs_mul, Int.natAbs_natCast, h1] at h
      exact hrp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h)
    constructor <;> intro h
    · exact key 1 (by exact_mod_cast h) rfl
    · exact key (-1) (by exact_mod_cast h) rfl

  let J : Submodule ℤ ℍ[ℚ, a, b] := Λ.map (LinearMap.mulRight ℤ π)
  have memJ : ∀ x, x ∈ J ↔ ∃ l ∈ Λ, l * π = x := fun x => by
    simp only [J, Submodule.mem_map, LinearMap.mulRight_apply]
  have hJle : J ≤ Λ := by
    intro x hx; obtain ⟨l, hl, rfl⟩ := (memJ x).1 hx; exact hO.mul_mem hl hπ
  have hJr : ∀ y ∈ Λ, (r : ℤ) • y ∈ J := by
    intro y hy
    refine (memJ _).2 ⟨((n : ℚ) : ℍ[ℚ, a, b]) * (y * star π), hO.mul_mem (intCast_mem hO n) (hO.mul_mem hy hsπ), ?_⟩
    have e : ((n : ℚ) : ℍ[ℚ, a, b]) * (y * star π) * π = (((r : ℚ)) : ℍ[ℚ, a, b]) * y := by
      rw [mul_assoc, mul_assoc, star_mul_eq_coe_nrd, hn, ← coe_commutes ((r : ℚ) * n) y, ← mul_assoc, ← coe_mul]
      congr 2
      rw [mul_comm ((r : ℚ)) n, ← mul_assoc, hnn, one_mul]
    rw [e, zsmul_eq_mul, Int.cast_natCast, coe_natCast]
  have hJstab : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
    intro m hm x hx; obtain ⟨l, hl, rfl⟩ := (memJ x).1 hx
    exact (memJ _).2 ⟨m * l, hO.mul_mem hm hl, mul_assoc m l π⟩
  obtain ⟨-, hclass⟩ :=
    QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq hB Λ hΛ r hr
  have hJP : ∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n' : ℤ, nrd x = (r : ℚ) * n' := by
    rcases hclass J hJle hJr hJstab with hJ1 | hJ2 | hJ3
    · exfalso
      obtain ⟨y, hy, hyπ⟩ := (hJ1 π).1 ((memJ _).2 ⟨1, hO.one_mem, one_mul _⟩)
      obtain ⟨k, hk⟩ := nrd_int hO hy
      have h3 : nrd π = (r : ℚ) ^ 2 * k := by
        rw [hyπ, zsmul_eq_mul, Int.cast_natCast, ← coe_natCast, nrd_mul, nrd_coe, hk]
      rw [hn, sq, mul_assoc] at h3
      have h4 : (n : ℚ) = r * k := mul_left_cancel₀ hr0 h3
      rcases Int.natAbs_eq_iff.mp (show n.natAbs = 1 from by
        have : ((n : ℚ)) * n = 1 := hnn
        have : n * n = 1 := by exact_mod_cast this
        rcases Int.eq_one_or_neg_one_of_mul_eq_one this with h | h <;> simp [h]) with h | h
      · rw [h] at h4; exact (hr_ndvd_one k).1 (by push_cast at h4; linarith)
      · rw [h] at h4; exact (hr_ndvd_one k).2 (by push_cast at h4; linarith)
    · exact hJ2
    · exfalso
      have h1 : (1 : ℍ[ℚ, a, b]) ∈ J := hJ3.symm ▸ hO.one_mem
      obtain ⟨l, hl, hl1⟩ := (memJ 1).1 h1
      obtain ⟨k, hk⟩ := nrd_int hO hl
      have h3 : nrd l * nrd π = 1 := by rw [← nrd_mul, hl1, nrd_one]
      rw [hn, hk] at h3
      rcases Int.natAbs_eq_iff.mp (show n.natAbs = 1 from by
        have : ((n : ℚ)) * n = 1 := hnn
        have : n * n = 1 := by exact_mod_cast this
        rcases Int.eq_one_or_neg_one_of_mul_eq_one this with h | h <;> simp [h]) with h | h
      · rw [h] at h3; exact (hr_ndvd_one k).1 (by push_cast at h3; linarith)
      · rw [h] at h3; exact (hr_ndvd_one k).2 (by push_cast at h3; linarith)
  have hgen : ∀ m ∈ Λ, (∃ n : ℤ, nrd m = (r : ℚ) * n) ↔ ∃ l ∈ Λ, m = l * π := by
    intro m hm
    constructor
    · intro hD; obtain ⟨l, hl, hlm⟩ := (memJ m).1 ((hJP m).2 ⟨hm, hD⟩); exact ⟨l, hl, hlm.symm⟩
    · rintro ⟨l, hl, rfl⟩; exact ((hJP _).1 ((memJ _).2 ⟨l, hl, rfl⟩)).2
  obtain ⟨G1, G2⟩ :=
    QuaternionAlgebra.IsMaximalOrder.forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt
      hB Λ hΛ r hr π hπ hgen
  exact ⟨π, hπ, hnrd, G1, G2, hgen⟩

end S_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt (solution)
