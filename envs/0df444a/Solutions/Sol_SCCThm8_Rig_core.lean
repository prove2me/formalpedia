-- Prove2me | solution 1 for SCCThm8.Rig.core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:21.188729+00:00
-- url     : https://prove2.me/submissions/a29a7f49-4bde-4d4f-8176-2a0d0484896e

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_card_compl_fin
public import Theorems.Thm_SCCThm8_Rig_exists_kset
public import Theorems.Thm_SCCThm8_Rig_const_of_swap
public import Theorems.Thm_SCCThm8_Rig_prod_sw
public import Theorems.Thm_SCCThm8_Rig_comm_id
public import Theorems.Thm_SCCThm8_Rig_prod_ind

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
namespace SCCThm8.Rig
theorem _root_.solution {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {H : Type*} [CommGroup H] (φ : H →* G) (g' : Fin (3 * k) → H)
    (hs1 : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A →
      f₁ (sw A i j) = φ (g' j * (g' i)⁻¹) * f₁ A)
    (hs3 : ∀ C : Finset (Fin (3 * k)), C.card = k → ∀ j i, j ∈ C → i ∉ C →
      f₃ (sw C j i) = f₃ C * φ (g' i * (g' j)⁻¹))
    (A B C : Finset (Fin (3 * k))) (hA : A.card = k) (hB : B.card = k) (hC : C.card = k) :
    f₁ A * f₂ B * f₃ C = φ (∏ i, g' i ^ (mult A B C i - 1)) := by
  set P : Finset (Fin (3 * k)) → H := fun S => ∏ x ∈ S, g' x with hPdef
  have c1 := const_of_swap (k := k) (fun S => (φ (P S))⁻¹ * f₁ S) (by
    intro S hS i j hi hj
    simp only [hPdef]
    rw [prod_sw g' hi hj, hs1 S hS i j hi hj]
    simp only [map_mul, map_inv]
    group)
  have c3 := const_of_swap (k := k) (fun S => f₃ S * (φ (P S))⁻¹) (by
    intro S hS j i hj hi
    simp only [hPdef]
    rw [prod_sw g' hj hi, mul_comm _ (∏ x ∈ S, g' x), hs3 S hS j i hj hi]
    simp only [map_mul, map_inv]
    group)
  obtain ⟨A₀, hA₀, -, hA₀B⟩ := exists_kset (k := k) ∅ B (by simp) (by simp) (by omega)
  set C₀ := (A₀ ∪ B)ᶜ with hC₀
  have hC₀c : C₀.card = k := by
    rw [hC₀, card_compl_fin, card_union_of_disjoint hA₀B]; omega
  have hA₀C₀ : Disjoint A₀ C₀ := by
    rw [disjoint_left]; intro x hx hxC; simp [hC₀] at hxC; exact hxC.1 hx
  have hBC₀ : Disjoint B C₀ := by
    rw [disjoint_left]; intro x hx hxC; simp [hC₀] at hxC; exact hxC.2 hx
  have h0 := hP A₀ B C₀ hA₀ hB hC₀c hA₀B hA₀C₀ hBC₀
  have e1 : (φ (P A))⁻¹ * f₁ A = (φ (P A₀))⁻¹ * f₁ A₀ := c1 _ A A₀ hA hA₀ rfl
  have e3 : f₃ C * (φ (P C))⁻¹ = f₃ C₀ * (φ (P C₀))⁻¹ := c3 _ C C₀ hC hC₀c rfl
  have hf1 : f₁ A = φ (P A) * ((φ (P A₀))⁻¹ * f₁ A₀) := by rw [← e1]; group
  have hf3 : f₃ C = (f₃ C₀ * (φ (P C₀))⁻¹) * φ (P C) := by rw [← e3]; group
  have hf2 : f₂ B = (f₁ A₀)⁻¹ * (f₃ C₀)⁻¹ := by
    calc f₂ B = (f₁ A₀)⁻¹ * (f₁ A₀ * f₂ B * f₃ C₀) * (f₃ C₀)⁻¹ := by group
      _ = _ := by rw [h0]; group
  have hU : ∏ i, g' i = P A₀ * P B * P C₀ := by
    rw [← prod_compl_mul_prod (A₀ ∪ B), prod_union hA₀B, ← hC₀, mul_comm]
  have hR : ∏ i, g' i ^ (mult A B C i - 1) = P A * P B * P C * (∏ i, g' i)⁻¹ := by
    simp only [hPdef, mult, zpow_sub, zpow_add, zpow_one, prod_mul_distrib, prod_inv_distrib, prod_ind]
  rw [hR, hU, ← comm_id, hf1, hf2, hf3]
  simp only [map_mul, map_inv]
  group
end SCCThm8.Rig
