-- Prove2me | solution 1 for SizeRamsey.Plan.erase_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:29.436554+00:00
-- url     : https://prove2.me/submissions/9d7f1be8-a086-43ea-8cfd-ac47a8cbe6c5

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_cross_count
public import Theorems.Thm_SizeRamsey_Plan_erase_degree_eq
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
    edgeCount (erase G D) + (∑ v ∈ D, G.degree v) =
      edgeCount G + edgeCount (G.induce (D : Set V)) := by
  have hE : ∑ v ∈ Finset.univ.filter (· ∉ D), ((G.neighborFinset v).filter (· ∉ D)).card =
      2 * edgeCount (erase G D) := by
    rw [edgeCount_eq_card, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [Finset.sum_subtype (p := (· ∉ D)) _ (by simp)]
    exact Finset.sum_congr rfl fun v _ => (erase_degree_eq G D v).symm
  have hI : ∑ v ∈ D, ((G.neighborFinset v).filter (· ∈ D)).card =
      2 * edgeCount (G.induce (D : Set V)) := by
    rw [edgeCount_eq_card, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [Finset.sum_subtype (p := (· ∈ D)) _ (by simp)]
    exact Finset.sum_congr rfl fun v _ => (induce_finset_degree_eq G D v).symm
  have hG : ∑ v, G.degree v = 2 * edgeCount G := by
    rw [edgeCount_eq_card, SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hsplit : ∀ v, G.degree v = ((G.neighborFinset v).filter (· ∈ D)).card +
      ((G.neighborFinset v).filter (· ∉ D)).card := fun v => by
    rw [← G.card_neighborFinset_eq_degree, Finset.card_filter_add_card_filter_not]
  have hD : Finset.univ.filter (· ∈ D) = D := by ext; simp
  have hU : ∑ v, G.degree v = ∑ v ∈ D, G.degree v +
      ∑ v ∈ Finset.univ.filter (· ∉ D), G.degree v := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ D), hD]
  have hDs : ∑ v ∈ D, G.degree v = ∑ v ∈ D, ((G.neighborFinset v).filter (· ∈ D)).card +
      ∑ v ∈ D, ((G.neighborFinset v).filter (· ∉ D)).card := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun v _ => hsplit v
  have hNs : ∑ v ∈ Finset.univ.filter (· ∉ D), G.degree v =
      ∑ v ∈ Finset.univ.filter (· ∉ D), ((G.neighborFinset v).filter (· ∈ D)).card +
      ∑ v ∈ Finset.univ.filter (· ∉ D), ((G.neighborFinset v).filter (· ∉ D)).card := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun v _ => hsplit v
  have hC := cross_count G D
  omega
end SizeRamsey.Plan
