-- Prove2me | solution 1 for SizeRamsey.Plan.induce_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:18:38.957614+00:00
-- url     : https://prove2.me/submissions/29b28143-b9b1-42d7-acab-ee38ee59bb99

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (s : Set V) (v : s) :
    (G.induce s).degree v = ((G.neighborFinset v.val).filter (· ∈ s)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext w
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coe_subtype,
    Finset.mem_filter, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.2⟩
  · rintro ⟨ha, hs⟩
    exact ⟨⟨w, hs⟩, ha, rfl⟩
end SizeRamsey.Plan
