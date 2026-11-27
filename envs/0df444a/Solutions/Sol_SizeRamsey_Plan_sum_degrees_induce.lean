-- Prove2me | solution 1 for SizeRamsey.Plan.sum_degrees_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:28.307725+00:00
-- url     : https://prove2.me/submissions/a9f2ff48-de3c-4b5c-9e70-0b91aec0607f

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_induce_degree_eq
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (s : Set V) :
    ∑ v ∈ Finset.univ.filter (· ∈ s), ((G.neighborFinset v).filter (· ∈ s)).card =
      2 * edgeCount (G.induce s) := by
  rw [edgeCount_eq_card, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [Finset.sum_subtype (p := (· ∈ s)) _ (by simp)]
  exact Finset.sum_congr rfl fun v _ => (induce_degree_eq G s v).symm
end SizeRamsey.Plan
