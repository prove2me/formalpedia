-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_delete_leaf_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:34.084112+00:00
-- url     : https://prove2.me/submissions/59b106e8-1137-495f-89e5-8dfb5e950db8

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_rotate
public import Theorems.Thm_SizeRamsey_Plan_tau4_erase_eq_of

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (v : V) (hd : G.degree v ≤ 1) :
    tau4 (erase G {v}) = tau4 G := by
  refine tau4_erase_eq_of G G {v} (fun f hf i hi => ?_) (fun _ _ _ _ => Iff.rfl)
  rw [Finset.mem_singleton] at hi
  obtain ⟨hinj, h01, -, -, h30⟩ := IsC4Map.rotate hf i
  simp only [zero_add] at h01 h30
  rw [hi] at h01 h30
  have hne : f (1 + i) ≠ f (3 + i) := fun h13 => by
    have : (1 : Fin 4) = 3 := hinj (a₁ := 1) (a₂ := 3) h13
    exact absurd this (by decide)
  have hsub : ({f (1 + i), f (3 + i)} : Finset V) ⊆ G.neighborFinset v := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with rfl | rfl
    · exact h01
    · exact h30.symm
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne, SimpleGraph.card_neighborFinset_eq_degree] at this
  omega
end SizeRamsey.Plan
