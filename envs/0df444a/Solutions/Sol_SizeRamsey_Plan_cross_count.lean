-- Prove2me | solution 1 for SizeRamsey.Plan.cross_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:54.802397+00:00
-- url     : https://prove2.me/submissions/2a8b10f0-ce83-4375-82e4-094ef659d0ee

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_card_filter_neighborFinset

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (D : Finset V) :
    ∑ v ∈ Finset.univ.filter (· ∉ D), ((G.neighborFinset v).filter (· ∈ D)).card =
      ∑ v ∈ D, ((G.neighborFinset v).filter (· ∉ D)).card := by
  simp_rw [card_filter_neighborFinset]
  rw [Finset.sum_comm]
  have hD : Finset.univ.filter (· ∈ D) = D := by ext; simp
  rw [hD]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
  simp [G.adj_comm]
end SizeRamsey.Plan
