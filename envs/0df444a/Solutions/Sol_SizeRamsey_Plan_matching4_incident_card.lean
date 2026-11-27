-- Prove2me | solution 1 for SizeRamsey.Plan.matching4_incident_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:40.83759+00:00
-- url     : https://prove2.me/submissions/ee203fe0-c3da-4537-a326-9575814b7df5

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase
public import Theorems.Thm_SizeRamsey_Plan_incidentRed_adj

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*}
    (F : SimpleGraph V) (S : Finset V)
    (h : HasMatching4 (incidentRed F S)) :
    4 ≤ S.card := by
  classical
  obtain ⟨f, hf, h01, h23, h45, h67⟩ := h
  have pick : ∀ a b : Fin 8, (incidentRed F S).Adj (f a) (f b) →
      ∃ k, (k = a ∨ k = b) ∧ f k ∈ S := fun a b hab =>
    ((incidentRed_adj F S _ _).1 hab).2.elim (fun h => ⟨a, Or.inl rfl, h⟩)
      (fun h => ⟨b, Or.inr rfl, h⟩)
  obtain ⟨k0, hk0, hs0⟩ := pick _ _ h01
  obtain ⟨k1, hk1, hs1⟩ := pick _ _ h23
  obtain ⟨k2, hk2, hs2⟩ := pick _ _ h45
  obtain ⟨k3, hk3, hs3⟩ := pick _ _ h67
  have hcard : ({k0, k1, k2, k3} : Finset (Fin 8)).card = 4 := by
    rcases hk0 with rfl | rfl <;> rcases hk1 with rfl | rfl <;>
      rcases hk2 with rfl | rfl <;> rcases hk3 with rfl | rfl <;> decide
  have hsub : ({k0, k1, k2, k3} : Finset (Fin 8)).image f ⊆ S := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rcases hk with rfl | rfl | rfl | rfl <;> assumption
  calc 4 = (({k0, k1, k2, k3} : Finset (Fin 8)).image f).card := by
        rw [Finset.card_image_of_injective _ hf, hcard]
    _ ≤ S.card := Finset.card_le_card hsub
end SizeRamsey.Plan
