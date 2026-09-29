-- Prove2me | solution 1 for QuaternionAlgebra.star_image_smul_eq_mulRight_image_star_image_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/85fef1f3-8002-538e-afef-854f87fe9fbc

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_star_image_smul_eq_mulRight_image_star_image_smul_iff

set_option autoImplicit false
open scoped Quaternion Pointwise

noncomputable section

namespace QuatA6

variable {a b : ℚ}

theorem mem_smul_iff' (d : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) :
    z ∈ ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ↔ ∃ w ∈ I, (d : ℍ[ℚ, a, b]) * w = z :=
  Submodule.mem_smul_pointwise_iff_exists z d I

theorem image_eq_image_mul_of_smul {K K' : Set ℍ[ℚ, a, b]} {I J : Submodule ℤ ℍ[ℚ, a, b]}
    (d d' δ : (ℍ[ℚ, a, b])ˣ) (hJ : J = δ • I)
    (hK : K = star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hK' : K' = star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    K' = (· * star ((d' * δ * d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) '' K := by
  subst hK hK' hJ
  have key : ∀ w : ℍ[ℚ, a, b], star ((d : ℍ[ℚ, a, b]) * w) * star ((d' * δ * d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) =
      star ((d' : ℍ[ℚ, a, b]) * ((δ : ℍ[ℚ, a, b]) * w)) := by
    intro w
    rw [← star_mul, Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul_cancel_left]
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_smul_iff' d' _ w').mp hw'
    obtain ⟨w, hw, rfl⟩ := (mem_smul_iff' δ _ t).mp ht
    exact ⟨star ((d : ℍ[ℚ, a, b]) * w), ⟨_, (mem_smul_iff' d I _).mpr ⟨w, hw, rfl⟩, rfl⟩, key w⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (mem_smul_iff' d I v).mp hv
    exact ⟨_, (mem_smul_iff' d' _ _).mpr ⟨_, (mem_smul_iff' δ I _).mpr ⟨w, hw, rfl⟩, rfl⟩, (key w).symm⟩

theorem exists_smul_of_image_eq_image_mul {K K' : Set ℍ[ℚ, a, b]} {I J : Submodule ℤ ℍ[ℚ, a, b]}
    (d d' c : (ℍ[ℚ, a, b])ˣ)
    (hK : K = star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hK' : K' = star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (h : K' = (· * (c : ℍ[ℚ, a, b])) '' K) : J = (d'⁻¹ * star c * d) • I := by
  subst hK hK'
  have key : ∀ w : ℍ[ℚ, a, b], star ((d : ℍ[ℚ, a, b]) * w) * (c : ℍ[ℚ, a, b]) =
      star ((star c : (ℍ[ℚ, a, b])ˣ) * (d : ℍ[ℚ, a, b]) * w) := by
    intro w
    simp only [star_mul, Units.coe_star, star_star, mul_assoc]
  have h1 : ∀ t ∈ J, ∃ w ∈ I, (d' : ℍ[ℚ, a, b]) * t = (star c : (ℍ[ℚ, a, b])ˣ) * (d : ℍ[ℚ, a, b]) * w := by
    intro t ht
    have : star ((d' : ℍ[ℚ, a, b]) * t) ∈ star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) :=
      ⟨_, (mem_smul_iff' d' J _).mpr ⟨t, ht, rfl⟩, rfl⟩
    rw [h] at this
    obtain ⟨_, ⟨v, hv, rfl⟩, hz⟩ := this
    obtain ⟨w, hw, rfl⟩ := (mem_smul_iff' d I v).mp hv
    have hz' : star ((d : ℍ[ℚ, a, b]) * w) * (c : ℍ[ℚ, a, b]) = star ((d' : ℍ[ℚ, a, b]) * t) := hz
    rw [key] at hz'
    exact ⟨w, hw, (star_injective hz').symm⟩
  have h2 : ∀ w ∈ I, ∃ t ∈ J, (d' : ℍ[ℚ, a, b]) * t = (star c : (ℍ[ℚ, a, b])ˣ) * (d : ℍ[ℚ, a, b]) * w := by
    intro w hw
    have : star ((d : ℍ[ℚ, a, b]) * w) * (c : ℍ[ℚ, a, b]) ∈
        (· * (c : ℍ[ℚ, a, b])) '' (star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :=
      ⟨_, ⟨_, (mem_smul_iff' d I _).mpr ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    rw [← h] at this
    obtain ⟨_, hv, hz⟩ := this
    obtain ⟨t, ht, rfl⟩ := (mem_smul_iff' d' J _).mp hv
    rw [key] at hz
    exact ⟨t, ht, star_injective hz⟩
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := h1 z hz
    have hz' : z = ((d'⁻¹ * star c * d : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * w := by
      rw [Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc ((star c : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]),
        ← hzw, Units.inv_mul_cancel_left]
    rw [hz']
    exact Submodule.smul_mem_pointwise_smul w _ I hw
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z _ I).mp hz
    obtain ⟨t, ht, htw⟩ := h2 w hw
    have hz' : ((d'⁻¹ * star c * d : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * w = t := by
      rw [Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc ((star c : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]),
        ← htw, Units.inv_mul_cancel_left]
    show ((d'⁻¹ * star c * d : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * w ∈ J
    rw [hz']
    exact ht

end QuatA6

theorem solution
    {a b : ℚ} (I J : Submodule ℤ ℍ[ℚ, a, b]) (d d' c : (ℍ[ℚ, a, b])ˣ) :
    star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) =
        (· * (c : ℍ[ℚ, a, b])) '' (star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) ↔
      J = (d'⁻¹ * star c * d) • I := by
  constructor
  · intro h
    exact QuatA6.exists_smul_of_image_eq_image_mul d d' c rfl rfl h
  · intro hJ
    have := QuatA6.image_eq_image_mul_of_smul (K := star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
      (K' := star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) d d' (d'⁻¹ * star c * d) hJ rfl rfl
    have e : d' * (d'⁻¹ * star c * d) * d⁻¹ = star c := by group
    rw [e, Units.coe_star, star_star] at this
    exact this

end

end S_QuaternionAlgebra_star_image_smul_eq_mulRight_image_star_image_smul_iff
end P2MW
export P2MW.S_QuaternionAlgebra_star_image_smul_eq_mulRight_image_star_image_smul_iff (solution)
