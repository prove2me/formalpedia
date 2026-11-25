-- Prove2me | solution 1 for PerfectGraph.exists_clique_card_eq_cliqueNum_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:27:32.341187+00:00
-- url     : https://prove2.me/submissions/6e90e000-73a3-4bd6-ac29-3604428ef4e8

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution (S : Finset V) :
    ∃ K ⊆ S, G.IsClique (K : Set V) ∧ K.card = (G.induce (S : Set V)).cliqueNum := by
  obtain ⟨s, hs⟩ := (G.induce (S : Set V)).exists_isNClique_cliqueNum
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp
  · intro x hx y hy hxy
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have := hs.isClique hx hy (fun h => hxy (congrArg Subtype.val h))
    simpa using this
  · simp [hs.card_eq]
end PerfectGraph
