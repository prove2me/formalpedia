-- Prove2me | solution 1 for SCCThm8.PRig.swap_idP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:32.577803+00:00
-- url     : https://prove2.me/submissions/05d10a76-d999-4e1c-b6fc-79fce25d09d0

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_ctx
public import Theorems.Thm_SCCThm8_Rig_card_compl_fin
public import Theorems.Thm_SCCThm8_Rig_swap_id


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
namespace SCCThm8.PRig
theorem _root_.solution (hP : Good k f₁ f₂ f₃) {A C : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hC : ∀ j, (C j).card = k) (hAC : ∀ j, Disjoint (A j) (C j))
    {j : Fin m} {s t : Fin (3 * k)} (hs : s ∈ A j) (ht : t ∈ C j) :
    f₁ (update A j (sw (A j) s t)) * (f₁ A)⁻¹ = (f₃ (update C j (sw (C j) t s)))⁻¹ * f₃ C := by
  let B : Fin m → Finset (Fin (3 * k)) := fun j => (A j ∪ C j)ᶜ
  have hB : ∀ j, (B j).card = k := fun j => by
    simp only [B]; rw [card_compl_fin, card_union_of_disjoint (hAC j), hA j, hC j]; omega
  have hD : ∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j) := by
    intro j
    refine ⟨?_, hAC j, ?_⟩
    · rw [disjoint_left]; intro x hx hxB; simp [B] at hxB; exact hxB.1 hx
    · rw [disjoint_left]; intro x hxB hx; simp [B] at hxB; exact hxB.2 hx
  have := Rig.swap_id (f₁ := fun X => f₁ (update A j X)) (f₂ := fun Y => f₂ (update B j Y))
    (f₃ := fun Z => f₃ (update C j Z)) (ctx hP hA hB hC hD j) (hA j) (hC j) (hAC j) hs ht
  simpa only [update_eq_self] using this
end SCCThm8.PRig
