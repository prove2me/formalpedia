-- Prove2me | solution 1 for SCCThm8.Rig.f3_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:45.936277+00:00
-- url     : https://prove2.me/submissions/5033ee42-66fb-4884-ac33-b890fbd7c164

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_exists_kset
public import Theorems.Thm_SCCThm8_Rig_swap_id
public import Theorems.Thm_SCCThm8_Rig_dl_spec

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
    (C : Finset (Fin (3 * k))) (hC : C.card = k) (j i : Fin (3 * k)) (hj : j ∈ C) (hi : i ∉ C) :
    f₃ (sw C j i) = f₃ C * (dl k f₁ i j)⁻¹ := by
  obtain ⟨A, hA, hiA, hAC⟩ := exists_kset (k := k) {i} C (by simp [hi]) (by rw [card_singleton]; omega) (by omega)
  have hi' : i ∈ A := hiA (mem_singleton_self i)
  have hjA : j ∉ A := fun h => disjoint_left.mp hAC h hj
  have e := swap_id hP hA hC hAC hi' hj
  rw [dl_spec hk hP A hA i j hi' hjA] at e
  have e' : dl k f₁ i j = (f₃ (sw C j i))⁻¹ * f₃ C := by rw [← e]; group
  rw [e']; group
end SCCThm8.Rig
