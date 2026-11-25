-- Prove2me | solution 1 for SimpleGraph.card_orderedTriangles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:31.24485+00:00
-- url     : https://prove2.me/submissions/6f754e3e-460c-429a-ac6f-f203c78077ea

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
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
public import Theorems.Thm_SimpleGraph_RamseyBound_symm
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
omit [Fintype V] in
/-- A `3`-set has six ordered triples of distinct elements. -/
private theorem card_distinct_triples [DecidableEq V] (s : Finset V) :
    #{x ∈ s ×ˢ s ×ˢ s | x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2} =
      #s * ((#s - 1) * (#s - 1) - (#s - 1)) := by
  rw [card_filter, sum_product, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun x hx => ?_
  rw [← card_erase_of_mem hx, ← offDiag_card, ← card_filter]
  congr 1
  ext ⟨y, z⟩
  simp only [mem_filter, mem_product, mem_offDiag, mem_erase]
  constructor
  · rintro ⟨⟨hy, hz⟩, hxy, hxz, hyz⟩
    exact ⟨⟨Ne.symm hxy, hy⟩, ⟨Ne.symm hxz, hz⟩, hyz⟩
  · rintro ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩, hyz⟩
    exact ⟨⟨hy, hz⟩, Ne.symm hxy, Ne.symm hxz, hyz⟩
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
theorem _root_.solution [DecidableEq V] :
    #G.orderedTriangles = 6 * #(G.cliqueFinset 3) := by
  rw [card_eq_sum_card_fiberwise (f := fun x : V × V × V => ({x.1, x.2.1, x.2.2} : Finset V))
    (t := G.cliqueFinset 3)]
  · rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun s hs => ?_
    have hs := mem_cliqueFinset_iff.mp hs
    have h6 := card_distinct_triples s
    rw [hs.card_eq, show 3 * ((3 - 1) * (3 - 1) - (3 - 1)) = 6 from rfl] at h6
    rw [← h6]
    congr 1
    ext ⟨x, y, z⟩
    simp only [orderedTriangles, mem_filter, mem_univ, true_and, mem_product]
    constructor
    · rintro ⟨⟨hxy, hxz, hyz⟩, rfl⟩
      exact ⟨⟨by simp, by simp, by simp⟩, hxy.ne, hxz.ne, hyz.ne⟩
    · rintro ⟨⟨hx, hy, hz⟩, hxy, hxz, hyz⟩
      refine ⟨⟨hs.isClique hx hy hxy, hs.isClique hx hz hxz, hs.isClique hy hz hyz⟩, ?_⟩
      refine eq_of_subset_of_card_le (by simp [insert_subset_iff, hx, hy, hz]) ?_
      rw [hs.card_eq, card_insert_of_notMem (by simp [hxy, hxz]),
        card_pair hyz]
  · intro x hx
    have hx := mem_coe.mp hx
    simp only [orderedTriangles, mem_filter, mem_univ, true_and] at hx
    change {x.1, x.2.1, x.2.2} ∈ (G.cliqueFinset 3 : Set (Finset V))
    rw [mem_coe, mem_cliqueFinset_iff, is3Clique_iff]
    exact ⟨_, _, _, hx.1, hx.2.1, hx.2.2, rfl⟩
end SimpleGraph
