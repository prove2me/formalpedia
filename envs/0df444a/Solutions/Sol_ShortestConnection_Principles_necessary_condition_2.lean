-- Prove2me | solution 1 for ShortestConnection.Principles.necessary_condition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:58:06.733857+00:00
-- url     : https://prove2.me/submissions/7e02453c-1139-4cf4-8d11-2f1d99e6dca2

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

set_option autoImplicit false

namespace SSSCutA0E

open ShortestConnection.Principles

/-- A path leaving a vertex set crosses it at an edge whose removal keeps both ends linked. -/
theorem cross {V : Type*} {H : SimpleGraph V} (S : Set V) :
    ∀ {u v : V} (p : H.Walk u v), p.IsPath → u ∈ S → v ∉ S →
      ∃ x y : V, x ∈ S ∧ y ∉ S ∧ H.Adj x y ∧
        (H.deleteEdges {s(x, y)}).Reachable u x ∧ (H.deleteEdges {s(x, y)}).Reachable y v ∧
        x ∈ p.support ∧ y ∈ p.support := by
  intro u v p
  induction p with
  | nil => intro _ hu hv; exact absurd hu hv
  | @cons u w v h q ih =>
    intro hp hu hv
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hq, hun⟩ := hp
    by_cases hw : w ∈ S
    · obtain ⟨x, y, hx, hy, hxy, h1, h2, hxs, hys⟩ := ih hq hw hv
      refine ⟨x, y, hx, hy, hxy, ?_, h2, ?_, ?_⟩
      · have hne : s(u, w) ≠ s(x, y) := by
          intro he
          rcases Sym2.eq_iff.mp he with ⟨h3, _⟩ | ⟨h3, _⟩
          · exact hun (h3 ▸ hxs)
          · exact hun (h3 ▸ hys)
        have hadj : (H.deleteEdges {s(x, y)}).Adj u w := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨h, by simpa using hne⟩
        exact hadj.reachable.trans h1
      · simp [hxs]
      · simp [hys]
    · refine ⟨u, w, hu, hw, h, SimpleGraph.Reachable.refl _, ?_, by simp, by simp⟩
      have hnot : s(u, w) ∉ q.edges := fun he => hun (q.fst_mem_support_of_mem_edges he)
      exact ⟨q.toDeleteEdge _ hnot⟩

theorem reach_of_adj {V : Type*} {H K : SimpleGraph V} (h : ∀ u v, H.Adj u v → K.Reachable u v)
    {u v : V} (p : H.Reachable u v) : K.Reachable u v := by
  obtain ⟨p⟩ := p
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h _ _ ha).trans ih

theorem card_link {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (F : Finset (Sym2 V)) (hF : (F : Set (Sym2 V)) ⊆ G.edgeSet) :
    Nat.card (linkGraph F).edgeSet = F.card := by
  have : (linkGraph F).edgeSet = (F : Set (Sym2 V)) := by
    unfold linkGraph
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · intro he; exact he.1
    · intro he
      refine ⟨he, ?_⟩
      exact G.not_isDiag_of_mem_edgeSet (hF he)
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]


/-- Exchange: a crossing `G`-edge not in an SSS is no shorter than some crossing `F`-link. -/
theorem exch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : IsSSS G w F) (S : Set V) (a b : V) (ha : a ∈ S) (hb : b ∉ S)
    (hab : G.Adj a b) (he : s(a, b) ∉ F) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y ∧ s(x, y) ∈ F ∧ w s(x, y) ≤ w s(a, b) := by
  obtain ⟨⟨hFG, hTree⟩, hFmin⟩ := hF
  obtain ⟨p⟩ := hTree.1.preconnected a b
  obtain ⟨x, y, hx, hy, hxy, h1, h2, -, -⟩ := cross S p.bypass p.bypass_isPath ha hb
  have hfF : s(x, y) ∈ F := ((SimpleGraph.fromEdgeSet_adj _).mp hxy).1
  have hGxy : G.Adj x y := hFG hfF
  refine ⟨x, y, hx, hy, hGxy, hfF, ?_⟩
  set F' := insert s(a, b) (F.erase s(x, y)) with hF'
  have hF'G : (F' : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he'
    rw [hF', Finset.coe_insert, Set.mem_insert_iff] at he'
    rcases he' with rfl | he'
    · exact hab
    · exact hFG (Finset.mem_of_mem_erase he')
  have hmono : ∀ u v : V, ((linkGraph F).deleteEdges {s(x, y)}).Adj u v →
      (linkGraph F').Adj u v := by
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    obtain ⟨h3, h4⟩ := huv
    unfold linkGraph at h3 ⊢
    rw [SimpleGraph.fromEdgeSet_adj] at h3 ⊢
    refine ⟨?_, h3.2⟩
    have : s(u, v) ∈ F' := by
      rw [hF']
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_erase]
      exact ⟨by simpa using h4, h3.1⟩
    exact_mod_cast this
  have hR : ∀ {u v : V}, ((linkGraph F).deleteEdges {s(x, y)}).Reachable u v →
      (linkGraph F').Reachable u v :=
    fun r => reach_of_adj (fun u v h => (hmono u v h).reachable) r
  have hab' : (linkGraph F').Adj a b := by
    unfold linkGraph
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, hab.ne⟩
    have : s(a, b) ∈ F' := by rw [hF']; exact Finset.mem_insert_self _ _
    exact_mod_cast this
  have hxy' : (linkGraph F').Reachable x y :=
    (hR h1).symm.trans (hab'.reachable.trans (hR h2).symm)
  have hconn : (linkGraph F').Connected := by
    have : Nonempty V := ⟨a⟩
    refine SimpleGraph.Connected.mk ?_
    intro u v
    refine reach_of_adj ?_ (hTree.1.preconnected u v)
    intro u' v' h
    by_cases hf : s(u', v') = s(x, y)
    · rcases Sym2.eq_iff.mp hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy'
      · exact hxy'.symm
    · apply SimpleGraph.Adj.reachable
      apply hmono
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨h, by simpa using hf⟩
  have hcardF' : F'.card = F.card := by
    rw [hF', Finset.card_insert_of_notMem (fun h => he (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hfF]
    have : 0 < F.card := Finset.card_pos.mpr ⟨_, hfF⟩
    omega
  have htree' : (linkGraph F').IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [card_link F' hF'G, hcardF', ← card_link F hFG]
    exact ((SimpleGraph.isTree_iff_connected_and_card).mp hTree).2
  have hle := hFmin F' ⟨hF'G, htree'⟩
  unfold length at hle
  rw [hF', Finset.sum_insert (fun h => he (Finset.mem_of_mem_erase h)),
    Finset.sum_erase_eq_sub hfF] at hle
  linarith

end SSSCutA0E

open ShortestConnection.Principles in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hF : IsSSS G w F) (S : Finset V) (hS : S.Nonempty) (hSu : S ≠ Finset.univ)
    (hfrag : ((linkGraph F).induce (S : Set V)).Connected) :
    ∃ u ∈ S, ∃ n ∉ S, G.Adj u n ∧ s(u, n) ∈ F ∧
      ∀ u' ∈ S, ∀ n' ∉ S, G.Adj u' n' → w s(u, n) ≤ w s(u', n') := by
  classical
  obtain ⟨u0, hu0⟩ := hS
  obtain ⟨v0, hv0⟩ : ∃ v, v ∉ S := by
    by_contra h
    push_neg at h
    exact hSu (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨p⟩ := hG.preconnected u0 v0
  obtain ⟨a0, b0, ha0, hb0, hab0, -⟩ :=
    SSSCutA0E.cross (H := G) (S : Set V) p.bypass p.bypass_isPath (by simpa using hu0)
      (by simpa using hv0)
  set C : Finset (V × V) := Finset.univ.filter (fun q => q.1 ∈ S ∧ q.2 ∉ S ∧ G.Adj q.1 q.2)
    with hC
  have hCne : C.Nonempty := ⟨(a0, b0), by simp [hC]; exact ⟨by simpa using ha0, by simpa using hb0, hab0⟩⟩
  obtain ⟨⟨a, b⟩, habC, hmin⟩ := C.exists_min_image (fun q => w s(q.1, q.2)) hCne
  simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at habC
  obtain ⟨ha, hb, hab⟩ := habC
  have hmin' : ∀ u' ∈ S, ∀ n' ∉ S, G.Adj u' n' → w s(a, b) ≤ w s(u', n') := by
    intro u' hu' n' hn' h
    exact hmin (u', n') (by simp [hC]; exact ⟨hu', hn', h⟩)
  by_cases hin : s(a, b) ∈ F
  · exact ⟨a, ha, b, hb, hab, hin, hmin'⟩
  · obtain ⟨x, y, hx, hy, hxy, hxyF, hle⟩ :=
      SSSCutA0E.exch G w F hF (S : Set V) a b (by simpa using ha) (by simpa using hb) hab hin
    refine ⟨x, by simpa using hx, y, by simpa using hy, hxy, hxyF, ?_⟩
    intro u' hu' n' hn' h
    exact hle.trans (hmin' u' hu' n' hn' h)
