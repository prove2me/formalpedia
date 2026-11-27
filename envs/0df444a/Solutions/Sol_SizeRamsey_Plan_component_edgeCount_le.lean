-- Prove2me | solution 1 for SizeRamsey.Plan.component_edgeCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:58.803798+00:00
-- url     : https://prove2.me/submissions/35d14ee0-941a-49a0-b255-fa6709456080

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
public import Theorems.Thm_SizeRamsey_Plan_sum_degrees_induce
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
theorem _root_.solution (C : G.ConnectedComponent) :
    edgeCount (compGraph G C) ≤ edgeCount G := by
  have h1 := sum_degrees_induce G C.supp
  have h2 : ∑ v ∈ Finset.univ.filter (· ∈ C.supp),
      ((G.neighborFinset v).filter (· ∈ C.supp)).card ≤ ∑ v, G.degree v := by
    refine (Finset.sum_le_sum fun v _ => ?_).trans
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_filter_le _ _
  have h3 : ∑ v, G.degree v = 2 * edgeCount G := by
    rw [edgeCount_eq_card, SimpleGraph.sum_degrees_eq_twice_card_edges]
  unfold compGraph
  omega
end SizeRamsey.Plan
