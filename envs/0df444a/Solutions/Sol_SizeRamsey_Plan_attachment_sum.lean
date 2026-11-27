-- Prove2me | solution 1 for SizeRamsey.Plan.attachment_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:32.095095+00:00
-- url     : https://prove2.me/submissions/d22540a1-8803-4d47-a677-d098ded58e97

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
public import Theorems.Thm_SizeRamsey_Plan_card_filter_neighborFinset
public import Theorems.Thm_SizeRamsey_Plan_cross_count
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
    (∑ C : (erase G D).ConnectedComponent,
      (attachmentEdges G D C).card) +
      2 * edgeCount (G.induce (D : Set V)) =
        ∑ v ∈ D, G.degree v := by
  set g : V → ℕ := fun a => ((G.neighborFinset a).filter (· ∈ D)).card with hg
  have hD : Finset.univ.filter (· ∈ D) = D := by ext; simp
  have hatt : ∀ C : (erase G D).ConnectedComponent,
      (attachmentEdges G D C).card = ∑ a ∈ componentVerts G D C, g a := by
    intro C
    unfold attachmentEdges
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = ((G.neighborFinset a).filter (· ∈ D)).card
    rw [card_filter_neighborFinset, hD]
  have hcv : ∀ C : (erase G D).ConnectedComponent,
      ∑ a ∈ componentVerts G D C, g a =
        ∑ x ∈ Finset.univ.filter (fun x => (erase G D).connectedComponentMk x = C), g x.val := by
    intro C
    unfold componentVerts
    rw [Finset.sum_image fun x _ y _ h => Subtype.ext h]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x; simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hall : ∑ C : (erase G D).ConnectedComponent, (attachmentEdges G D C).card =
      ∑ v ∈ Finset.univ.filter (· ∉ D), g v := by
    simp_rw [hatt, hcv]
    refine Eq.trans ?_ (Finset.sum_subtype (p := (· ∉ D)) (F := inferInstance) (Finset.univ.filter (· ∉ D)) (by simp) g).symm
    convert Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := (erase G D).connectedComponentMk) (fun _ _ => Finset.mem_univ _)
      (fun x => g x.val) using 3
  have hI : ∑ v ∈ D, ((G.neighborFinset v).filter (· ∈ D)).card =
      2 * edgeCount (G.induce (D : Set V)) := by
    rw [edgeCount_eq_card, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [Finset.sum_subtype (p := (· ∈ D)) _ (by simp)]
    exact Finset.sum_congr rfl fun v _ => (induce_finset_degree_eq G D v).symm
  have hDs : ∑ v ∈ D, G.degree v = ∑ v ∈ D, ((G.neighborFinset v).filter (· ∈ D)).card +
      ∑ v ∈ D, ((G.neighborFinset v).filter (· ∉ D)).card := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← G.card_neighborFinset_eq_degree, Finset.card_filter_add_card_filter_not]
  have hC := cross_count G D
  rw [hall, hDs, ← hI, ← hC]
  ac_rfl
end SizeRamsey.Plan
