-- Prove2me | solution 1 for SCCThm8.Rig.swap_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:35.976429+00:00
-- url     : https://prove2.me/submissions/3729f006-8ce9-4b3e-8454-f896894a0138

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_mem_sw
public import Theorems.Thm_SCCThm8_Rig_card_sw
public import Theorems.Thm_SCCThm8_Rig_card_compl_fin

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}
namespace SCCThm8.Rig
theorem _root_.solution
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {A C : Finset (Fin (3 * k))} (hA : A.card = k) (hC : C.card = k) (hAC : Disjoint A C)
    {i j : Fin (3 * k)} (hi : i ∈ A) (hj : j ∈ C) :
    f₁ (sw A i j) * (f₁ A)⁻¹ = (f₃ (sw C j i))⁻¹ * f₃ C := by
  have hij : i ≠ j := fun h => disjoint_left.mp hAC hi (h ▸ hj)
  have hjA : j ∉ A := fun h => disjoint_left.mp hAC h hj
  have hiC : i ∉ C := fun h => disjoint_left.mp hAC hi h
  set B := (A ∪ C)ᶜ with hB
  have hBc : B.card = k := by rw [hB, card_compl_fin, card_union_of_disjoint hAC]; omega
  have hAB : Disjoint A B := by
    rw [disjoint_left]; intro x hx hxB; simp [hB] at hxB; exact hxB.1 hx
  have hBC : Disjoint B C := by
    rw [disjoint_left]; intro x hxB hx; simp [hB] at hxB; exact hxB.2 hx
  have h1 := hP A B C hA hBc hC hAB hAC hBC
  have hA'B : Disjoint (sw A i j) B := by
    rw [disjoint_left]; intro x hx hxB; simp [hB] at hxB
    rcases mem_sw.mp hx with rfl | ⟨_, h⟩
    · exact hxB.2 hj
    · exact hxB.1 h
  have hBC' : Disjoint B (sw C j i) := by
    rw [disjoint_left]; intro x hxB hx; simp [hB] at hxB
    rcases mem_sw.mp hx with rfl | ⟨_, h⟩
    · exact hxB.1 hi
    · exact hxB.2 h
  have hA'C' : Disjoint (sw A i j) (sw C j i) := by
    rw [disjoint_left]; intro x hx hx'
    rcases mem_sw.mp hx with rfl | ⟨h1, h2⟩ <;> rcases mem_sw.mp hx' with h3 | ⟨h3, h4⟩
    · exact hij h3.symm
    · exact h3 rfl
    · exact h1 h3
    · exact disjoint_left.mp hAC h2 h4
  have h2 := hP (sw A i j) B (sw C j i) (card_sw hA hi hjA) hBc (card_sw hC hj hiC) hA'B hA'C' hBC'
  have e1 : f₂ B = (f₁ A)⁻¹ * (f₃ C)⁻¹ := by
    calc f₂ B = (f₁ A)⁻¹ * (f₁ A * f₂ B * f₃ C) * (f₃ C)⁻¹ := by group
      _ = _ := by rw [h1]; group
  rw [e1] at h2
  calc f₁ (sw A i j) * (f₁ A)⁻¹
      = (f₁ (sw A i j) * ((f₁ A)⁻¹ * (f₃ C)⁻¹) * f₃ (sw C j i)) * (f₃ (sw C j i))⁻¹ * f₃ C := by
        group
    _ = (f₃ (sw C j i))⁻¹ * f₃ C := by rw [h2]; group
end SCCThm8.Rig
