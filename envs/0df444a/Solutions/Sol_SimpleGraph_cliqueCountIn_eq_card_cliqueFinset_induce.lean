-- Prove2me | solution 1 for SimpleGraph.cliqueCountIn_eq_card_cliqueFinset_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:10.158214+00:00
-- url     : https://prove2.me/submissions/1f806cb3-b60f-4a83-828a-4a1b34265ede

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (S : Finset V) (k : ℕ) :
    G.cliqueCountIn S k = #((G.induce (S : Set V)).cliqueFinset k) := by
  rw [cliqueCountIn]
  symm
  refine card_bij (fun T _ => T.map (Function.Embedding.subtype _)) (fun T hT => ?_)
    (fun a _ b _ h => Finset.map_injective _ h) fun T hT => ?_
  · rw [mem_cliqueFinset_iff, isNClique_iff, isClique_induce_iff] at hT
    simp only [mem_filter, mem_powersetCard, card_map, hT.2, and_true, coe_map,
      Function.Embedding.coe_subtype, hT.1]
    intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.mp hx
    exact y.2
  · simp only [mem_filter, mem_powersetCard] at hT
    refine ⟨T.subtype (· ∈ S), ?_, subtype_map_of_mem fun x hx => hT.1.1 hx⟩
    rw [mem_cliqueFinset_iff, isNClique_iff, isClique_induce_iff, card_subtype,
      filter_true_of_mem fun x hx => hT.1.1 hx, hT.1.2]
    refine ⟨?_, rfl⟩
    convert hT.2
    ext x
    simp only [Set.mem_image, mem_coe, mem_subtype, Subtype.exists, exists_and_right,
      exists_eq_right]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hT.1.1 h, h⟩⟩
end SimpleGraph
