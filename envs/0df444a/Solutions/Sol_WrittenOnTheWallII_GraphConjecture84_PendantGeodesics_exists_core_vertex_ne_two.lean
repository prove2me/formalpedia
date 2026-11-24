-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.exists_core_vertex_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:49.079229+00:00
-- url     : https://prove2.me/submissions/e20da174-1ab2-4239-953d-c24efd1e105a

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hcard : 3 ≤ K.card) (a b : α) :
    ∃ v : ↥(K : Set α), (v : α) ≠ a ∧ (v : α) ≠ b := by
  classical
  by_contra! hn
  have hsub : K ⊆ {a, b} := by
    intro v hv
    by_cases hva : v = a
    · simp [hva]
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hn ⟨v, hv⟩ hva))
  have hle := Finset.card_le_card hsub
  have htwo : ({a, b} : Finset α).card ≤ 2 := Finset.card_le_two
  omega
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
