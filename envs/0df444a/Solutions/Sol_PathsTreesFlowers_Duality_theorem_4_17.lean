-- Prove2me | solution 1 for PathsTreesFlowers.Duality.theorem_4_17
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:04:16.906792+00:00
-- url     : https://prove2.me/submissions/13b4aacd-d44c-447e-8af5-baad565048b2

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_2

namespace SolPathsTreesFlowersTheorem417

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma mem_verts_of_mem_edges {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {e : E} (he : e ∈ J.edges)
    {v : V} (hv : v ∈ G.ends e) : v ∈ J.verts := by
  have hsub := J.toSub.edges_sub e he
  exact (Finset.mem_sym2_iff.mp hsub) v hv

lemma mem_compl_verts_of_mem_deleteSub {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {e : E}
    (he : e ∈ (deleteSub G J.toSub).edges) {v : V} (hv : v ∈ G.ends e) : v ∉ J.verts := by
  have hsub := (deleteSub G J.toSub).edges_sub e he
  have hmem := (Finset.mem_sym2_iff.mp hsub) v hv
  exact (Finset.mem_sdiff.mp hmem).2

lemma disjoint_deleteSub_edges {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {M₁ MJ : Finset E}
    (hM₁ : M₁ ⊆ (deleteSub G J.toSub).edges) (hMJ : MJ ⊆ J.edges) : Disjoint M₁ MJ := by
  rw [Finset.disjoint_left]
  intro e he₁ heJ
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have ha1 : a ∉ J.verts := mem_compl_verts_of_mem_deleteSub J (hM₁ he₁) (by rw [hab]; simp)
  have ha2 : a ∈ J.verts := mem_verts_of_mem_edges J (hMJ heJ) (by rw [hab]; simp)
  exact ha1 ha2

lemma isMatching_union_deleteSub {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {M₁ MJ : Finset E}
    (hM₁ : IsMatchingIn G (deleteSub G J.toSub) M₁)
    (hMJ : MJ ⊆ J.edges) (hMJ_match : IsMatching G MJ) :
    IsMatching G (M₁ ∪ MJ) := by
  intro e he f hf hef v hve hvf
  rcases Finset.mem_union.mp he with he₁ | heJ <;> rcases Finset.mem_union.mp hf with hf₁ | hfJ
  · exact hM₁.2 e he₁ f hf₁ hef v hve hvf
  · exact mem_compl_verts_of_mem_deleteSub J (hM₁.1 he₁) hve (mem_verts_of_mem_edges J (hMJ hfJ) hvf)
  · exact mem_compl_verts_of_mem_deleteSub J (hM₁.1 hf₁) hvf (mem_verts_of_mem_edges J (hMJ heJ) hve)
  · exact hMJ_match e heJ f hfJ hef v hve hvf

lemma exists_inner_of_not_mem_deleteSub {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) (hJ : IsHungarianTree G J)
    {e : E} (he : e ∉ (deleteSub G J.toSub).edges) : ∃ u ∈ J.inner, u ∈ G.ends e := by
  simp only [deleteSub, induced, edgesWithin, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sym2_iff, Finset.mem_sdiff, not_forall, Classical.not_imp, not_not] at he
  rcases he with ⟨x, hxe, hxJ⟩
  change x ∈ J.inner ∪ J.outer at hxJ
  rcases Finset.mem_union.mp hxJ with hxi | hxo
  · exact ⟨x, hxi, hxe⟩
  · obtain ⟨w, hwi, hends⟩ := hJ e x hxo hxe
    exact ⟨w, hwi, by rw [hends]; simp⟩

lemma card_le_inner_of_every_edge_meets_inner {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {M' : Finset E}
    (hM' : IsMatching G M') (hmeet : ∀ e ∈ M', ∃ u ∈ J.inner, u ∈ G.ends e) :
    M'.card ≤ J.inner.card := by
  classical
  have hsub : M' ⊆ J.inner.biUnion (fun u => M'.filter (fun e => u ∈ G.ends e)) := by
    intro e he
    obtain ⟨u, hu, hue⟩ := hmeet e he
    exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨he, hue⟩⟩
  calc M'.card ≤ (J.inner.biUnion (fun u => M'.filter (fun e => u ∈ G.ends e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ u ∈ J.inner, (M'.filter (fun e => u ∈ G.ends e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ J.inner, 1 := by
        refine Finset.sum_le_sum fun u _ => Finset.card_le_one.mpr ?_
        intro e₁ he₁ e₂ he₂
        simp only [Finset.mem_filter] at he₁ he₂
        by_contra hne
        exact hM' e₁ he₁.1 e₂ he₂.1 hne u he₁.2 he₂.2
    _ = J.inner.card := by simp

lemma card_eq_inner_of_isMaxMatchingIn {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {MJ : Finset E}
    (hMJ : IsMaxMatchingIn G J.toSub MJ) : MJ.card = J.inner.card := by
  classical
  have hle : MJ.card ≤ J.inner.card := by
    refine card_le_inner_of_every_edge_meets_inner J hMJ.2.1 fun e he => ?_
    obtain ⟨u, hu, w, _, h⟩ := J.edge_ends e (hMJ.1 he)
    exact ⟨u, hu, by rw [h]; simp⟩
  have hge : J.inner.card ≤ MJ.card := by
    obtain ⟨v, hv, hexp⟩ := (lemma_4_2 G J).2.2 MJ hMJ
    have hsub : J.inner ⊆ MJ.biUnion (fun e => J.inner.filter (fun u => u ∈ G.ends e)) := by
      intro u hu
      have hu_verts : u ∈ J.verts := Finset.mem_union_left _ hu
      have huv : u ≠ v := fun h => Finset.disjoint_left.mp J.disjoint hu (h ▸ hv)
      have hnot_exp : ¬ PathsTreesFlowers.Duality.IsExposed G MJ u := fun hex => huv ((hexp u hu_verts).mp hex)
      simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp
      rcases hnot_exp with ⟨e, he, hue⟩
      exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hu, hue⟩⟩
    calc J.inner.card ≤ (MJ.biUnion (fun e => J.inner.filter (fun u => u ∈ G.ends e))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ e ∈ MJ, (J.inner.filter (fun u => u ∈ G.ends e)).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ MJ, 1 := by
          refine Finset.sum_le_sum fun e he => Finset.card_le_one.mpr ?_
          intro u₁ hu₁ u₂ hu₂
          simp only [Finset.mem_filter] at hu₁ hu₂
          obtain ⟨u, hu, w, hw, h⟩ := J.edge_ends e (hMJ.1 he)
          have h1 : u₁ = u ∨ u₁ = w := by simpa [h] using hu₁.2
          have h2 : u₂ = u ∨ u₂ = w := by simpa [h] using hu₂.2
          have hnw : w ∉ J.inner := Finset.disjoint_right.mp J.disjoint hw
          rcases h1 with rfl | rfl
          · rcases h2 with rfl | rfl
            · rfl
            · exact absurd hu₂.1 hnw
          · exact absurd hu₁.1 hnw
      _ = MJ.card := by simp
  exact le_antisymm hle hge

end SolPathsTreesFlowersTheorem417

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality
open SolPathsTreesFlowersTheorem417

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (J : AltTree G) (hJ : IsHungarianTree G J)
    (M₁ : Finset E) (hM₁ : IsMatchingIn G (deleteSub G J.toSub) M₁) :
    IsMaxMatchingIn G (deleteSub G J.toSub) M₁ ↔
      ∀ MJ : Finset E, IsMaxMatchingIn G J.toSub MJ → IsMaxMatching G (M₁ ∪ MJ) := by
  classical
  constructor
  · intro hMax₁ MJ hMJ
    refine ⟨isMatching_union_deleteSub J hM₁ hMJ.1 hMJ.2.1, fun M' hM' => ?_⟩
    set M'_del := M'.filter (fun e => e ∈ (deleteSub G J.toSub).edges)
    set M'_in := M'.filter (fun e => e ∉ (deleteSub G J.toSub).edges)
    have hsplit : M'.card = M'_del.card + M'_in.card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have hdel_le : M'_del.card ≤ M₁.card := by
      refine hMax₁.2.2 M'_del (fun e he => (Finset.mem_filter.mp he).2) ?_
      intro e he f hf hef v hve hvf
      exact hM' e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hef v hve hvf
    have hin_le : M'_in.card ≤ J.inner.card := by
      refine card_le_inner_of_every_edge_meets_inner J
        (fun e he f hf hef v hve hvf =>
          hM' e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hef v hve hvf)
        fun e he => exists_inner_of_not_mem_deleteSub J hJ (Finset.mem_filter.mp he).2
    have hMJ_card : MJ.card = J.inner.card := card_eq_inner_of_isMaxMatchingIn J hMJ
    have hunion_card : (M₁ ∪ MJ).card = M₁.card + MJ.card :=
      Finset.card_union_of_disjoint (disjoint_deleteSub_edges J hM₁.1 hMJ.1)
    omega
  · intro hall
    have houter_ne : J.outer.Nonempty := by
      rw [← Finset.card_pos, (lemma_4_2 G J).1]
      omega
    obtain ⟨v, hv⟩ := houter_ne
    obtain ⟨MJ, ⟨hMJ, -⟩, -⟩ := (lemma_4_2 G J).2.1 v hv
    have hMax := hall MJ hMJ
    refine ⟨hM₁.1, hM₁.2, fun M₁' hM₁'_sub hM₁'_match => ?_⟩
    have hM₁'_in : IsMatchingIn G (deleteSub G J.toSub) M₁' := ⟨hM₁'_sub, hM₁'_match⟩
    have hunion_match : IsMatching G (M₁' ∪ MJ) :=
      isMatching_union_deleteSub J hM₁'_in hMJ.1 hMJ.2.1
    have hle := hMax.2 (M₁' ∪ MJ) hunion_match
    rw [Finset.card_union_of_disjoint (disjoint_deleteSub_edges J hM₁'_sub hMJ.1),
      Finset.card_union_of_disjoint (disjoint_deleteSub_edges J hM₁.1 hMJ.1)] at hle
    omega
