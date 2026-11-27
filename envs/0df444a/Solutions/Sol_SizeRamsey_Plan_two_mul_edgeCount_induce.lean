-- Prove2me | solution 1 for SizeRamsey.Plan.two_mul_edgeCount_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:40.594712+00:00
-- url     : https://prove2.me/submissions/89a149fa-be12-4083-8509-9fa7452b9037

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_card_filter_neighborFinset
public import Theorems.Thm_SizeRamsey_Plan_induce_finset_degree_eq
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
theorem _root_.solution (D : Finset V) :
    2 * edgeCount (G.induce (D : Set V)) =
      ∑ x ∈ D, ∑ y ∈ D, if G.Adj x y then 1 else 0 := by
  rw [edgeCount_eq_card, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hD : Finset.univ.filter (· ∈ D) = D := by ext; simp
  refine Eq.trans ?_ (Finset.sum_subtype (p := (· ∈ D)) (F := inferInstance) D (fun _ => Iff.rfl)
    (fun x => ∑ y ∈ D, if G.Adj x y then 1 else 0)).symm
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [induce_finset_degree_eq G D x, card_filter_neighborFinset, hD]
end SizeRamsey.Plan
