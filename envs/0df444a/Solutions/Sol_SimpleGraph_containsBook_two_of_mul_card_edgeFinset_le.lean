-- Prove2me | solution 1 for SimpleGraph.containsBook_two_of_mul_card_edgeFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:55.147108+00:00
-- url     : https://prove2.me/submissions/45f54550-2459-47f7-a856-4ca3494c845e

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_containsBook_two_iff
public import Theorems.Thm_SimpleGraph_sum_card_commonNeighbors_eq
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_red
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_toBlue_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_toBlue_spine
public import Theorems.Thm_SimpleGraph_Bireservoir_toRed_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_toRed_spine
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_blue
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_pool
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_red
attribute [local simp] SimpleGraph.Bireservoir.ofPool_blue
attribute [local simp] SimpleGraph.Bireservoir.ofPool_pool
attribute [local simp] SimpleGraph.Bireservoir.ofPool_red
attribute [local simp] SimpleGraph.Bireservoir.redPivot_blue
attribute [local simp] SimpleGraph.Bireservoir.redPivot_pool
attribute [local simp] SimpleGraph.Bireservoir.redPivot_red
attribute [local simp] SimpleGraph.Bireservoir.toBlue_pool
attribute [local simp] SimpleGraph.Bireservoir.toBlue_spine
attribute [local simp] SimpleGraph.Bireservoir.toRed_pool
attribute [local simp] SimpleGraph.Bireservoir.toRed_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine


section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]
private theorem sum_card_neighborFinset : ∑ u, #(G.neighborFinset u) = 2 * #G.edgeFinset := by
  simp_rw [card_neighborFinset_eq_degree]
  exact G.sum_degrees_eq_twice_card_edges
private theorem exists_adj_le_of_le_sum (f : V → V → ℕ) {t : ℕ}
    (hE : G.edgeFinset.Nonempty)
    (h : t * (2 * #G.edgeFinset) ≤ ∑ u, ∑ v ∈ G.neighborFinset u, f u v) :
    ∃ u v, G.Adj u v ∧ t ≤ f u v := by
  by_contra! hlt
  have hsum : ∑ u, ∑ v ∈ G.neighborFinset u, f u v < ∑ u, ∑ v ∈ G.neighborFinset u, t := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      refine sum_lt_sum (fun u _ => sum_le_sum fun v hv => (hlt u v ?_).le) ⟨a, mem_univ _,
        sum_lt_sum (fun v hv => (hlt a v ?_).le) ⟨b, by simpa using he, hlt a b he⟩⟩
      · simpa using hv
      · simpa using hv
  simp_rw [sum_const, smul_eq_mul, ← sum_mul, sum_card_neighborFinset] at hsum
  rw [mul_comm] at h
  omega
end SimpleGraph
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution [DecidableEq V] {t : ℕ}
    (hE : G.edgeFinset.Nonempty) (h : t * #G.edgeFinset ≤ 3 * #(G.cliqueFinset 3)) :
    G.ContainsBook 2 t := by
  refine containsBook_two_iff.mpr (exists_adj_le_of_le_sum _ hE ?_)
  rw [sum_card_commonNeighbors_eq]
  linarith
end SimpleGraph
