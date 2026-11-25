-- Prove2me | solution 1 for SCCThm8.PRig.coreP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:23.198533+00:00
-- url     : https://prove2.me/submissions/4eb4bdc5-6adc-47de-9321-099c7eb0c359

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_constP
public import Theorems.Thm_SCCThm8_PRig_prodP_update
public import Theorems.Thm_SCCThm8_Rig_card_compl_fin
public import Theorems.Thm_SCCThm8_Rig_comm_id
public import Theorems.Thm_SCCThm8_Rig_exists_kset
public import Theorems.Thm_SCCThm8_Rig_prod_ind
public import Theorems.Thm_SCCThm8_Rig_prod_sw


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
namespace SCCThm8.PRig
theorem _root_.solution {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
    (hP : Good k f₁ f₂ f₃)
    {H : Type*} [CommGroup H] (φ : H →* G) (g' : Fin m → Fin (3 * k) → H)
    (hs1 : ∀ A : Fin m → Finset (Fin (3 * k)), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j →
      t ∉ A j → f₁ (update A j (sw (A j) s t)) = φ (g' j t * (g' j s)⁻¹) * f₁ A)
    (hs3 : ∀ C : Fin m → Finset (Fin (3 * k)), (∀ j, (C j).card = k) → ∀ j t s, t ∈ C j →
      s ∉ C j → f₃ (update C j (sw (C j) t s)) = f₃ C * φ (g' j s * (g' j t)⁻¹))
    (A B C : Fin m → Finset (Fin (3 * k))) (hA : ∀ j, (A j).card = k)
    (hB : ∀ j, (B j).card = k) (hC : ∀ j, (C j).card = k) :
    f₁ A * f₂ B * f₃ C = φ (∏ j, ∏ i, g' j i ^ (multP A B C j i - 1)) := by
  set P : (Fin m → Finset (Fin (3 * k))) → H := fun S => ∏ j, ∏ x ∈ S j, g' j x with hPdef
  have c1 := constP (k := k) (fun S => (φ (P S))⁻¹ * f₁ S) (by
    intro S hS j s t hs ht
    simp only [hPdef]
    rw [prodP_update, prod_sw (g' j) hs ht, mul_inv_cancel_right, hs1 S hS j s t hs ht]
    simp only [map_mul, map_inv]
    group)
  have c3 := constP (k := k) (fun S => f₃ S * (φ (P S))⁻¹) (by
    intro S hS j t s ht hs
    simp only [hPdef]
    rw [prodP_update, prod_sw (g' j) ht hs, mul_inv_cancel_right, hs3 S hS j t s ht hs,
      mul_comm (g' j s * (g' j t)⁻¹)]
    simp only [map_mul, map_inv]
    group)
  have hex : ∀ j, ∃ X : Finset (Fin (3 * k)), X.card = k ∧ (∅ : Finset (Fin (3 * k))) ⊆ X ∧
      Disjoint X (B j) := fun j => exists_kset (k := k) ∅ (B j) (by simp) (by simp)
        (by rw [hB j]; omega)
  choose A₀ hA₀ _ hA₀B using hex
  let C₀ : Fin m → Finset (Fin (3 * k)) := fun j => (A₀ j ∪ B j)ᶜ
  have hC₀c : ∀ j, (C₀ j).card = k := fun j => by
    simp only [C₀]; rw [card_compl_fin, card_union_of_disjoint (hA₀B j), hA₀ j, hB j]; omega
  have hA₀C₀ : ∀ j, Disjoint (A₀ j) (C₀ j) := by
    intro j; rw [disjoint_left]; intro x hx hxC; simp [C₀] at hxC; exact hxC.1 hx
  have hBC₀ : ∀ j, Disjoint (B j) (C₀ j) := by
    intro j; rw [disjoint_left]; intro x hx hxC; simp [C₀] at hxC; exact hxC.2 hx
  have h0 := hP A₀ B C₀ hA₀ hB hC₀c (fun j => ⟨hA₀B j, hA₀C₀ j, hBC₀ j⟩)
  have e1 : (φ (P A))⁻¹ * f₁ A = (φ (P A₀))⁻¹ * f₁ A₀ := c1 A A₀ hA hA₀
  have e3 : f₃ C * (φ (P C))⁻¹ = f₃ C₀ * (φ (P C₀))⁻¹ := c3 C C₀ hC hC₀c
  have hf1 : f₁ A = φ (P A) * ((φ (P A₀))⁻¹ * f₁ A₀) := by rw [← e1]; group
  have hf3 : f₃ C = (f₃ C₀ * (φ (P C₀))⁻¹) * φ (P C) := by rw [← e3]; group
  have hf2 : f₂ B = (f₁ A₀)⁻¹ * (f₃ C₀)⁻¹ := by
    calc f₂ B = (f₁ A₀)⁻¹ * (f₁ A₀ * f₂ B * f₃ C₀) * (f₃ C₀)⁻¹ := by group
      _ = _ := by rw [h0]; group
  have hU : ∏ j, ∏ i, g' j i = P A₀ * P B * P C₀ := by
    simp only [hPdef, ← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    rw [← prod_compl_mul_prod (A₀ j ∪ B j), prod_union (hA₀B j), mul_comm]
  have hR : ∏ j, ∏ i, g' j i ^ (multP A B C j i - 1) = P A * P B * P C * (∏ j, ∏ i, g' j i)⁻¹ := by
    simp only [hPdef, multP, mult, zpow_sub, zpow_add, zpow_one, prod_mul_distrib,
      prod_inv_distrib, prod_ind]
  rw [hR, hU, ← comm_id, hf1, hf2, hf3]
  simp only [map_mul, map_inv]
  group
end SCCThm8.PRig
