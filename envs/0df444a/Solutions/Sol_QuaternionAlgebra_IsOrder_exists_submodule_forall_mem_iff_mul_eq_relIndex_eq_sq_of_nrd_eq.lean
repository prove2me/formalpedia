-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c0396631-4329-5aeb-9f6d-f6304014d837

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_relIndex_span_mul_eq_sq_of_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq

set_option autoImplicit false

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ℓ : ℕ)
    (t : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (hnrd : nrd t = (ℓ : ℚ)) :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b],
      (∀ x : ℍ[ℚ, a, b], x ∈ J ↔ ∃ y ∈ Λ, y * t = x) ∧
      J ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ J) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ J → (y : ℍ[ℚ, a, b]) * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
  let f : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] := (AddMonoidHom.mulRight t).toIntLinearMap
  have hf : ∀ y : ℍ[ℚ, a, b], f y = y * t := fun y => rfl
  have hJ : Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => y * t) '' (Λ : Set ℍ[ℚ, a, b])) = Λ.map f := by
    have : (fun y : ℍ[ℚ, a, b] => y * t) '' (Λ : Set ℍ[ℚ, a, b]) = (Λ.map f : Set ℍ[ℚ, a, b]) := by
      rw [Submodule.map_coe]; rfl
    rw [this, Submodule.span_eq]

  obtain ⟨-, n, hn⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ ht
  have hstar : star t ∈ Λ := by
    have h1 : star t = ((trd t : ℚ) : ℍ[ℚ, a, b]) - t := by rw [← add_star_eq_coe_trd]; abel
    have h2 : ((trd t : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [← hn, zsmul_eq_mul, mul_one]; norm_cast
    rw [h1, h2]
    exact Λ.sub_mem (Λ.smul_mem n hΛ.one_mem) ht
  have hℓ : ∀ x : ℍ[ℚ, a, b], (ℓ : ℚ) • x = (x * star t) * t := by
    intro x
    rw [mul_assoc, star_mul_eq_coe_nrd, hnrd, ← QuaternionAlgebra.coe_commutes, QuaternionAlgebra.coe_mul_eq_smul]
  refine ⟨Λ.map f, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [Submodule.mem_map, hf]
  · rintro x ⟨y, hy, rfl⟩
    exact hΛ.mul_mem hy ht
  · intro x
    rw [hℓ]
    exact ⟨(x : ℍ[ℚ, a, b]) * star t, hΛ.mul_mem x.2 hstar, rfl⟩
  · rintro y x ⟨z, hz, rfl⟩
    exact ⟨(y : ℍ[ℚ, a, b]) * z, hΛ.mul_mem y.2 hz, by rw [hf, hf, mul_assoc]⟩
  · rw [← hJ]
    exact QuaternionAlgebra.relIndex_span_mul_eq_sq_of_nrd_eq Λ hΛ.fg hΛ.spanTop t
      (fun y hy => hΛ.mul_mem hy ht) ℓ (Or.inl hnrd)

end S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq (solution)
