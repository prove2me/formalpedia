-- Prove2me | solution 1 for SCCThm8.Rig.indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:10.728103+00:00
-- url     : https://prove2.me/submissions/3e070318-1964-4bbe-9076-3b0321080c7f

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_exists_kset
public import Theorems.Thm_SCCThm8_Rig_swap_id

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}
namespace SCCThm8.Rig
theorem _root_.solution (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {A A' : Finset (Fin (3 * k))} (hA : A.card = k) (hA' : A'.card = k) {i j : Fin (3 * k)}
    (hi : i ∈ A) (hi' : i ∈ A') (hj : j ∉ A) (hj' : j ∉ A') :
    f₁ (sw A i j) * (f₁ A)⁻¹ = f₁ (sw A' i j) * (f₁ A')⁻¹ := by
  obtain ⟨C, hC, hjC, hCd⟩ := exists_kset (k := k) {j} (A ∪ A') (by simp [hj, hj']) (by rw [card_singleton]; omega)
    (by have := card_union_le A A'; omega)
  have hjC' : j ∈ C := hjC (mem_singleton_self j)
  rw [swap_id hP hA hC (hCd.symm.mono_left subset_union_left) hi hjC',
    swap_id hP hA' hC (hCd.symm.mono_left subset_union_right) hi' hjC']
end SCCThm8.Rig
