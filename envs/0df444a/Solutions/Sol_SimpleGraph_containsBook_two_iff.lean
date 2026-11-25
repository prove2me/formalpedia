-- Prove2me | solution 1 for SimpleGraph.containsBook_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:15.340942+00:00
-- url     : https://prove2.me/submissions/a3792c82-2dbf-4fbc-8229-1f7e1c5e9511

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_card_commonNeighbors_eq_card_filter
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



set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {t : ℕ} :
    G.ContainsBook 2 t ↔ ∃ u v, G.Adj u v ∧ t ≤ Fintype.card (G.commonNeighbors u v) := by
  classical
  constructor
  · rintro ⟨R, hR, ht⟩
    obtain ⟨u, v, huv, hs⟩ := card_eq_two.mp hR
    have hu : u ∈ R.spine := by simp [hs]
    have hv : v ∈ R.spine := by simp [hs]
    refine ⟨u, v, R.isClique_spine hu hv huv, ht.trans ?_⟩
    rw [card_commonNeighbors_eq_card_filter]
    exact card_le_card fun w hw => mem_filter.mpr ⟨mem_univ _, R.adj u hu w hw, R.adj v hv w hw⟩
  · rintro ⟨u, v, huv, ht⟩
    refine ⟨⟨{u, v}, {w | G.Adj u w ∧ G.Adj v w}, ?_, ?_, ?_⟩, card_pair huv.ne, ?_⟩
    · rw [coe_pair]
      exact isClique_pair.mpr fun _ => huv
    · rw [Finset.disjoint_left]
      intro w hw hw'
      rw [mem_filter] at hw'
      rcases mem_insert.mp hw with rfl | hw
      · exact G.irrefl hw'.2.1
      · rw [mem_singleton.mp hw] at hw'
        exact G.irrefl hw'.2.2
    · intro x hx y hy
      rw [mem_filter] at hy
      rcases mem_insert.mp hx with rfl | hx
      · exact hy.2.1
      · rw [mem_singleton.mp hx]
        exact hy.2.2
    · rwa [← card_commonNeighbors_eq_card_filter]
end SimpleGraph
