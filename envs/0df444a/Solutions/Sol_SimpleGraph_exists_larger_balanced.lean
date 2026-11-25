-- Prove2me | solution 1 for SimpleGraph.exists_larger_balanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:59:24.328549+00:00
-- url     : https://prove2.me/submissions/a09056a2-45c2-48ff-9447-9a6207d2134f

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation
public import Theorems.Thm_SimpleGraph_Walk_countP_darts_fst_eq
public import Theorems.Thm_SimpleGraph_card_filter_toFinset_of_nodup
public import Theorems.Thm_SimpleGraph_card_image_edge_filter
public import Theorems.Thm_SimpleGraph_exists_closed_trail_avoiding


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (heven : ∀ v, Even (G.degree v)) {Ds : Finset G.Dart}
    (hinj : EdgeInj Ds) (hbal : Balanced Ds) {x y₀ : V} (hxy : G.Adj x y₀)
    (hnot : ∀ d ∈ Ds, d.edge ≠ s(x, y₀)) :
    ∃ Ds' : Finset G.Dart, EdgeInj Ds' ∧ Balanced Ds' ∧ Ds ⊆ Ds' ∧ Ds.card < Ds'.card := by
  set S := (Ds.image Dart.edge).toList
  have hSnd : S.Nodup := nodup_toList _
  have hSsub : ∀ e ∈ S, e ∈ G.edgeSet := by
    intro e he
    rw [mem_toList, mem_image] at he
    obtain ⟨d, -, rfl⟩ := he
    exact d.edge_mem
  have hpar : ∀ y, Even (S.countP fun e => y ∈ e) ↔ Even (G.degree y) := by
    intro y
    refine iff_of_true ?_ (heven y)
    rw [← card_filter_toFinset_of_nodup hSnd, toList_toFinset, card_image_edge_filter hinj,
      hbal y]
    exact ⟨_, rfl⟩
  have hnotS : s(x, y₀) ∉ S := by
    rw [mem_toList, mem_image]
    rintro ⟨d, hd, he⟩
    exact hnot d hd he
  obtain ⟨c, hc, hcpos, hcdisj⟩ := exists_closed_trail_avoiding hSnd hSsub hpar hxy hnotS
  have hdnd : c.darts.Nodup := List.Nodup.of_map Dart.edge hc.edges_nodup
  have hdisj : Disjoint Ds c.darts.toFinset := by
    rw [Finset.disjoint_left]
    intro d hd hdc
    have : d.edge ∈ c.edges := by
      rw [edges_eq_map_darts]; exact List.mem_map_of_mem (List.mem_toFinset.mp hdc)
    exact hcdisj _ this (by rw [mem_toList]; exact mem_image_of_mem _ hd)
  refine ⟨Ds ∪ c.darts.toFinset, ?_, ?_, subset_union_left, ?_⟩
  · intro d hd d' hd' he
    rcases mem_union.mp hd with hd | hd <;> rcases mem_union.mp hd' with hd' | hd'
    · exact hinj d hd d' hd' he
    · exfalso
      have : d'.edge ∈ c.edges := by
        rw [edges_eq_map_darts]; exact List.mem_map_of_mem (List.mem_toFinset.mp hd')
      exact hcdisj _ this (by rw [mem_toList, ← he]; exact mem_image_of_mem _ hd)
    · exfalso
      have : d.edge ∈ c.edges := by
        rw [edges_eq_map_darts]; exact List.mem_map_of_mem (List.mem_toFinset.mp hd)
      exact hcdisj _ this (by rw [mem_toList, he]; exact mem_image_of_mem _ hd')
    · exact List.inj_on_of_nodup_map (by rw [← edges_eq_map_darts]; exact hc.edges_nodup)
        (List.mem_toFinset.mp hd) (List.mem_toFinset.mp hd') he
  · intro v
    rw [filter_union, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj),
      card_union_of_disjoint (disjoint_filter_filter hdisj), hbal v,
      card_filter_toFinset_of_nodup hdnd, card_filter_toFinset_of_nodup hdnd,
      c.countP_darts_fst_eq v]
  · rw [card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hdnd, length_darts]
    omega
end SimpleGraph
