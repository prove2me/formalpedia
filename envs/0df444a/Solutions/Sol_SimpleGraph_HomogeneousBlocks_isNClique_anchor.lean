-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.isNClique_anchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:35:24.069905+00:00
-- url     : https://prove2.me/submissions/ab6bad48-62af-48a9-9123-bd22c34ebb3d

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_adj_of_quotient_adj
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_repEmbedding_apply
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_isNClique_map_rep
public import Theorems.Thm_SimpleGraph_IsClique_union_of_forall_adj
public import Theorems.Thm_SimpleGraph_RamseyBound_symm
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine


attribute [local simp] SimpleGraph.HomogeneousBlocks.repEmbedding_apply

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution [DecidableEq V] [DecidableEq ι] {m n : ℕ} {I : Finset ι}
    (hI : F.quotient.IsNClique m I) {i₀ : ι} (hi₀ : i₀ ∈ I) {t : Finset V}
    (ht : G.IsNClique n t) (hts : t ⊆ F.block i₀) :
    G.IsNClique (n + m - 1) (t ∪ (I.erase i₀).map F.repEmbedding) := by
  have hrest : G.IsNClique (m - 1) ((I.erase i₀).map F.repEmbedding) := by
    refine F.isNClique_map_rep ⟨hI.isClique.subset (by simp), ?_⟩
    rw [card_erase_of_mem hi₀, hI.card_eq]
  have hcross : ∀ x ∈ t, ∀ y ∈ (I.erase i₀).map F.repEmbedding, G.Adj x y := by
    intro x hx y hy
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
    have hj' := mem_erase.mp hj
    exact F.adj_of_quotient_adj (hI.isClique hi₀ hj'.2 (Ne.symm hj'.1)) (hts hx) (F.rep_mem j)
  have hdisj : Disjoint t ((I.erase i₀).map F.repEmbedding) :=
    Finset.disjoint_left.mpr fun x hx hy => (G.irrefl (hcross x hx x hy))
  refine ⟨?_, ?_⟩
  · rw [coe_union]
    exact ht.isClique.union_of_forall_adj hrest.isClique hcross
  · rw [card_union_of_disjoint hdisj, ht.card_eq, hrest.card_eq]
    have : 1 ≤ m := hI.card_eq ▸ card_pos.mpr ⟨i₀, hi₀⟩
    omega
end SimpleGraph.HomogeneousBlocks
