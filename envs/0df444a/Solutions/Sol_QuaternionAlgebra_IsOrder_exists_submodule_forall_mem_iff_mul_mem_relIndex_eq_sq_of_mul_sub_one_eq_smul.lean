-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/14c41dab-83fd-53aa-a995-b62159e13822

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul

set_option autoImplicit false

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ℓ : ℕ)
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : J ≤ Λ) (hℓJ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ J)
    (hJ_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ J → (y : ℍ[ℚ, a, b]) * x ∈ J)
    (hJ_index : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (w : ↥Λ) (hwu : ∃ w' : ↥Λ, ∃ y : ↥Λ, (w' : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ L₀ : Submodule ℤ ℍ[ℚ, a, b], L₀ ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀) ∧
      L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧

      (∀ z : ℍ[ℚ, a, b], z ∈ L₀ ↔ z ∈ Λ ∧ z * (w : ℍ[ℚ, a, b]) ∈ J) ∧

      (∀ x : ℍ[ℚ, a, b], x ∈ J ↔
        ∃ z ∈ L₀, ∃ y : ↥Λ, x = z * (w : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) := by
  obtain ⟨w', y₁, hy₁⟩ := hwu
  have hw'w : (w' : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]) = 1 + (ℓ : ℚ) • (y₁ : ℍ[ℚ, a, b]) := by
    rw [← hy₁]; abel

  have hkey : ∀ x : ℍ[ℚ, a, b],
      x * (w' : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]) = x + (ℓ : ℚ) • (x * (y₁ : ℍ[ℚ, a, b])) := by
    intro x
    rw [mul_assoc, hw'w, mul_add, mul_one, mul_smul_comm]
  let L₀ : Submodule ℤ ℍ[ℚ, a, b] :=
    { carrier := {z | z ∈ Λ ∧ z * (w : ℍ[ℚ, a, b]) ∈ J}
      add_mem' := fun {x y} hx hy => ⟨Λ.add_mem hx.1 hy.1, by rw [add_mul]; exact J.add_mem hx.2 hy.2⟩
      zero_mem' := ⟨Λ.zero_mem, by rw [zero_mul]; exact J.zero_mem⟩
      smul_mem' := fun n {x} hx => ⟨Λ.smul_mem n hx.1, by
        show (n • x) * (w : ℍ[ℚ, a, b]) ∈ J
        rw [smul_mul_assoc]; exact J.smul_mem n hx.2⟩ }
  have hmem : ∀ z : ℍ[ℚ, a, b], z ∈ L₀ ↔ z ∈ Λ ∧ z * (w : ℍ[ℚ, a, b]) ∈ J := fun z => Iff.rfl
  refine ⟨L₀, fun z hz => ((hmem z).1 hz).1, ?_, ?_, ?_, hmem, ?_⟩
  ·
    intro x
    refine (hmem _).2 ⟨hJ (hℓJ x), ?_⟩
    rw [smul_mul_assoc]
    exact hℓJ ⟨(x : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]), hΛ.mul_mem x.2 w.2⟩
  ·
    intro y x hx
    obtain ⟨hxΛ, hxw⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨hΛ.mul_mem y.2 hxΛ, ?_⟩
    rw [mul_assoc]
    exact hJ_left y _ hxw
  ·
    let f : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := AddMonoidHom.mulRight (w : ℍ[ℚ, a, b])
    have hL₀eq : L₀.toAddSubgroup = J.toAddSubgroup.comap f ⊓ Λ.toAddSubgroup := by
      ext z
      simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_inf, AddSubgroup.mem_comap, hmem]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    have hsup : Λ.toAddSubgroup.map f ⊔ J.toAddSubgroup = Λ.toAddSubgroup := by
      refine le_antisymm (sup_le ?_ ?_) fun x hx => ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact hΛ.mul_mem hz w.2
      · intro x hx; exact hJ hx
      · have hx' : x = x * (w' : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]) - (ℓ : ℚ) • (x * (y₁ : ℍ[ℚ, a, b])) := by
          rw [hkey]; abel
        rw [hx']
        refine AddSubgroup.sub_mem _ (AddSubgroup.mem_sup_left ⟨x * (w' : ℍ[ℚ, a, b]), hΛ.mul_mem hx w'.2, rfl⟩)
          (AddSubgroup.mem_sup_right ?_)
        exact hℓJ ⟨x * (y₁ : ℍ[ℚ, a, b]), hΛ.mul_mem hx y₁.2⟩
    rw [hL₀eq, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap,
      ← AddSubgroup.relIndex_sup_right (Λ.toAddSubgroup.map f) J.toAddSubgroup, hsup]
    exact hJ_index
  ·
    intro x
    constructor
    · intro hx
      have hxΛ : x ∈ Λ := hJ hx
      refine ⟨x * (w' : ℍ[ℚ, a, b]), (hmem _).2 ⟨hΛ.mul_mem hxΛ w'.2, ?_⟩,
        ⟨-(x * (y₁ : ℍ[ℚ, a, b])), Λ.neg_mem (hΛ.mul_mem hxΛ y₁.2)⟩, ?_⟩
      · rw [hkey]
        exact J.add_mem hx (hℓJ ⟨x * (y₁ : ℍ[ℚ, a, b]), hΛ.mul_mem hxΛ y₁.2⟩)
      · simp only [hkey, smul_neg]
        abel
    · rintro ⟨z, hz, y, rfl⟩
      exact J.add_mem ((hmem z).1 hz).2 (hℓJ y)

end S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul (solution)
