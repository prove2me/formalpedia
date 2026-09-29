-- Prove2me | solution 1 for ShortestConnection.Principles.complete_construction_isSpanningSubtree
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:29:09.690775+00:00
-- url     : https://prove2.me/submissions/500bc9ac-8084-433f-b66f-21ad7a7d539e

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- An application adds a `G`-edge joining two terminals that are not yet linked. -/
theorem aux_ccss_app {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) (h : IsApplication G w F e) :
    ∃ a b : V, G.Adj a b ∧ e = s(a, b) ∧ ¬ (linkGraph F).Reachable a b := by
  rcases h with ⟨t, n, hiso, hadj, he, -⟩ | ⟨u, n, -, hnr, hadj, he, -⟩
  · refine ⟨t, n, hadj, he, ?_⟩
    rintro ⟨p⟩
    cases p with
    | nil => exact hadj.ne rfl
    | cons h' _ => exact hiso _ h'
  · exact ⟨u, n, hadj, he, hnr⟩

theorem aux_ccss_insert {V : Type*} [DecidableEq V] (F : Finset (Sym2 V)) (a b : V) :
    linkGraph (insert s(a, b) F) = linkGraph F ⊔ SimpleGraph.edge a b := by
  unfold linkGraph SimpleGraph.edge
  rw [Finset.coe_insert, Set.insert_eq, SimpleGraph.fromEdgeSet_union, sup_comm]

theorem aux_ccss_inv {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (l : List (Sym2 V)) (hl : IsConstruction G w l) :
    ∀ i, i ≤ l.length → (linkGraph (l.take i).toFinset).IsAcyclic ∧ (l.take i).Nodup ∧
      ∀ e ∈ l.take i, e ∈ G.edgeSet := by
  intro i
  induction i with
  | zero => intro _; simp [linkGraph]
  | succ i ih =>
    intro hi
    have hi' : i < l.length := by omega
    obtain ⟨hac, hnd, hG⟩ := ih hi'.le
    obtain ⟨a, b, hab, he, hnr⟩ := aux_ccss_app G w _ _ (hl i hi')
    have htake : l.take (i + 1) = l.take i ++ [l[i]] := by
      exact List.take_succ_eq_append_getElem hi'
    have hnotin : l[i] ∉ l.take i := by
      intro hmem
      apply hnr
      apply SimpleGraph.Adj.reachable
      simp only [linkGraph, SimpleGraph.fromEdgeSet_adj, List.coe_toFinset, Set.mem_ofPred_eq]
      exact ⟨he ▸ hmem, hab.ne⟩
    rw [htake]
    refine ⟨?_, ?_, ?_⟩
    · have hfs : [l[i]].toFinset = {l[i]} := Finset.val_eq_singleton_iff.mp rfl
      rw [List.toFinset_append, hfs, Finset.union_comm,
        Finset.singleton_union, he, aux_ccss_insert]
      exact hac.sup_edge_of_not_reachable hnr
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rintro rfl
      exact hnotin hx
    · intro e hmem
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact hG e hmem
      · rw [he]; exact hab

end ShortestConnection.Principles

open ShortestConnection.Principles

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : IsCompleteConstruction G w l) :
    IsSpanningSubtree G l.toFinset := by
  obtain ⟨hcons, hlen⟩ := hl
  obtain ⟨hac, hnd, hGe⟩ := aux_ccss_inv G w l hcons l.length le_rfl
  rw [List.take_length] at hac hnd hGe
  have hsub : ((l.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    exact hGe e (by simpa using he)
  refine ⟨hsub, ?_⟩
  set T := linkGraph l.toFinset with hT
  have hTedge : T.edgeSet = (l.toFinset : Set (Sym2 V)) := by
    rw [hT, linkGraph, SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left,
      Set.disjoint_right]
    intro e hd he
    exact (G.not_isDiag_of_mem_edgeSet (hsub he)) hd
  have hTle : T ≤ G := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hTedge]
    exact hsub
  obtain ⟨T', hTT', hT'G, hT'⟩ := hG.exists_isTree_le_of_le_of_isAcyclic hTle hac
  have hcard' := (SimpleGraph.isTree_iff_connected_and_card.mp hT').2
  have hcardT : T.edgeSet.ncard = Fintype.card V - 1 := by
    rw [hTedge, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]
  have hpos : 0 < Fintype.card V := by
    have := hG.nonempty
    exact Fintype.card_pos
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hcard'
  have heq : T.edgeSet = T'.edgeSet := by
    apply Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hTT')
    · omega
  have : T = T' := SimpleGraph.edgeSet_inj.mp heq
  rw [this]
  exact hT'
