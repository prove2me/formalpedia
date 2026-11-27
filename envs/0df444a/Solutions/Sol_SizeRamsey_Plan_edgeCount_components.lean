-- Prove2me | solution 1 for SizeRamsey.Plan.edgeCount_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:58.110808+00:00
-- url     : https://prove2.me/submissions/63106bf1-db61-4f1b-a9b8-299e1c0b979d

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
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
theorem _root_.solution :
    edgeCount G =
      ∑ C : G.ConnectedComponent, edgeCount (compGraph G C) := by
  have hC : ∀ C : G.ConnectedComponent, 2 * edgeCount (compGraph G C) =
      ∑ v ∈ Finset.univ.filter (fun v => G.connectedComponentMk v = C), G.degree v := by
    intro C
    rw [edgeCount_eq_card, ← SimpleGraph.sum_degrees_eq_twice_card_edges,
      Finset.sum_subtype (p := (· ∈ C.supp)) _ (fun v => by simp)]
    exact Finset.sum_congr rfl fun v _ =>
      SimpleGraph.degree_induce_of_neighborSet_subset fun w hw => (C.mem_supp_congr_adj hw).mp v.2
  have hG : 2 * edgeCount G = ∑ v, G.degree v := by
    rw [edgeCount_eq_card, SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hsum : ∑ v, G.degree v = ∑ C : G.ConnectedComponent,
      ∑ v ∈ Finset.univ.filter (fun v => G.connectedComponentMk v = C), G.degree v :=
    (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
  have : 2 * edgeCount G = 2 * ∑ C : G.ConnectedComponent, edgeCount (compGraph G C) := by
    rw [hG, hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun C _ => (hC C).symm
  omega
end SizeRamsey.Plan
