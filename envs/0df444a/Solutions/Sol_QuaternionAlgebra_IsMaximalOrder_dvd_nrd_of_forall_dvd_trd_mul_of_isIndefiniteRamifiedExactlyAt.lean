-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/02f2ddf3-8365-5063-b758-3b2f7447dd53

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
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
    ∀ w ∈ Λ, (∀ z ∈ Λ, ∃ t : ℤ, trd (w * z) = (r : ℚ) * t) → ∃ n : ℤ, nrd w = (r : ℚ) * n := by
  classical
  intro w hw hwz
  have hO : IsOrder Λ := hΛ.1
  have hram := QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
    hB Λ hΛ r hr

  let J : Submodule ℤ ℍ[ℚ, a, b] :=
    { carrier := {x | x ∈ Λ ∧ ∀ z ∈ Λ, ∃ t : ℤ, trd (x * z) = (r : ℚ) * t}
      zero_mem' := ⟨Λ.zero_mem, fun z _ => ⟨0, by simp [B16R.trd_zero']⟩⟩
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Λ.add_mem hx hy, fun z hz => ?_⟩
        obtain ⟨s, hs⟩ := hx' z hz
        obtain ⟨t, ht⟩ := hy' z hz
        exact ⟨s + t, by rw [add_mul, B16R.trd_add', hs, ht]; push_cast; ring⟩
      smul_mem' := by
        rintro n x ⟨hx, hx'⟩
        refine ⟨Λ.smul_mem n hx, fun z hz => ?_⟩
        obtain ⟨s, hs⟩ := hx' z hz
        exact ⟨n * s, by rw [smul_mul_assoc, B16R.trd_zsmul', hs]; push_cast; ring⟩ }
  have hJΛ : J ≤ Λ := fun x hx => hx.1
  have hrJ : ∀ y ∈ Λ, (r : ℤ) • y ∈ J := by
    intro y hy
    refine ⟨Λ.smul_mem _ hy, fun z hz => ?_⟩
    obtain ⟨⟨t, -, ht, -⟩, -⟩ := hO.exists_int_trd_eq_and_nrd_eq (hO.mul_mem hy hz)
    exact ⟨t, by rw [smul_mul_assoc, B16R.trd_zsmul', ht]; push_cast; ring⟩
  have hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
    rintro m hm x ⟨hx, hx'⟩
    refine ⟨hO.mul_mem hm hx, fun z hz => ?_⟩
    obtain ⟨t, ht⟩ := hx' (z * m) (hO.mul_mem hz hm)
    exact ⟨t, by rw [mul_assoc, B16R.trd_mul_comm', mul_assoc, ht]⟩
  have hwJ : w ∈ J := ⟨hw, hwz⟩
  rcases hram.2 J hJΛ hrJ hleft with hJ | hJ | hJ
  · obtain ⟨y, hy, rfl⟩ := (hJ w).1 hwJ
    exact hram.1.2.1 y hy
  · exact ((hJ w).1 hwJ).2
  · exfalso
    have h1 : (1 : ℍ[ℚ, a, b]) ∈ J := by rw [hJ]; exact hO.one_mem
    have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
    rcases hrp.eq_two_or_odd with h2 | hodd
    ·
      obtain ⟨θ, hθ, t, n, hθt, hθn, hirr⟩ :=
        QuaternionAlgebra.IsMaximalOrder.exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
          hB Λ hΛ r hr
      obtain ⟨s, hs⟩ := h1.2 θ hθ
      rw [one_mul, hθt, h2] at hs
      have hts : t = 2 * s := by exact_mod_cast hs
      have h0 := hirr 0
      have h1' := hirr 1
      subst h2
      have hcast : ((2 * s : ℤ) : ZMod 2) = 0 := by
        have e : (2 : ZMod 2) = 0 := by decide
        push_cast
        rw [e, zero_mul]
      rw [hts, hcast] at h0 h1'
      have key : ∀ m : ZMod 2, m = 0 ∨ m = 1 := by decide
      rcases key (n : ZMod 2) with hn | hn <;> rw [hn] at h0 h1'
      · exact h0 (by decide)
      · exact h1' (by decide)
    · obtain ⟨s, hs⟩ := h1.2 1 hO.one_mem
      rw [one_mul, B16R.trd_one'] at hs
      have h2s : (2 : ℤ) = r * s := by exact_mod_cast hs
      have hdvd : (r : ℤ) ∣ 2 := ⟨s, h2s⟩
      have hr2 : r ∣ 2 := by exact_mod_cast hdvd
      have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hr2
      have := hrp.two_le
      omega

end S_QuaternionAlgebra_IsMaximalOrder_dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt (solution)
