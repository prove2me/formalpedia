-- Prove2me | solution 1 for OpenMath.exists_indep_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:16.702003+00:00
-- url     : https://prove2.me/submissions/3774b53f-085a-450a-a132-d312fcf01e48

module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Real.Basic
public import Definitions.Def_OpenMath_Common

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath
open SimpleGraph Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath
theorem _root_.solution (G : SimpleGraph α) (u : α) :
    ∃ S : Finset α, (∀ x ∈ S, G.Adj u x) ∧ (S : Set α).Pairwise (fun x y => ¬ G.Adj x y) ∧
      S.card = indepNeighborsCard G u := by
  classical
  obtain ⟨T, hT⟩ := (G.induce (G.neighborSet u)).exists_isNIndepSet_indepNum
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.mp hx
    exact y.2
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := mem_map.mp (mem_coe.mp hx)
    obtain ⟨y', hy', rfl⟩ := mem_map.mp (mem_coe.mp hy)
    have hne : x' ≠ y' := fun h => hxy (by rw [h])
    have := hT.isIndepSet (mem_coe.mpr hx') (mem_coe.mpr hy') hne
    simpa using this
  · rw [card_map, hT.card_eq]
    rfl
end OpenMath
