-- Prove2me | solution 1 for ShortestConnection.Principles.distinct_lengths_links_in_every_sss
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:08:45.056416+00:00
-- url     : https://prove2.me/submissions/6fe1f581-cb92-4364-9efe-f56099d65108

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

set_option autoImplicit false

namespace SSSCut474

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

/-- Cut property with distinct lengths. -/
theorem cut_mem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e f : Sym2 V, e ∈ G.edgeSet → f ∈ G.edgeSet → w e = w f → e = f)
    (F : Finset (Sym2 V)) (hF : IsSSS G w F) (S : Set V) (a b : V) (ha : a ∈ S) (hb : b ∉ S)
    (hab : G.Adj a b)
    (hmin : ∀ x y : V, x ∈ S → y ∉ S → G.Adj x y → w s(a, b) ≤ w s(x, y)) :
    s(a, b) ∈ F := by
  by_contra he
  obtain ⟨⟨hFG, hTree⟩, hFmin⟩ := hF
  obtain ⟨p⟩ := hTree.1.preconnected a b
  obtain ⟨x, y, hx, hy, hxy, h1, h2, -, -⟩ := cross S p.bypass p.bypass_isPath ha hb
  have hfF : s(x, y) ∈ F := ((SimpleGraph.fromEdgeSet_adj _).mp hxy).1
  have hGxy : G.Adj x y := hFG hfF
  have hne : s(a, b) ≠ s(x, y) := fun h => he (h ▸ hfF)
  have hlt : w s(a, b) < w s(x, y) := by
    refine lt_of_le_of_ne (hmin x y hx hy hGxy) ?_
    intro h
    exact hne (hw _ _ hab hGxy h)
  set F' := insert s(a, b) (F.erase s(x, y)) with hF'
  have hF'G : (F' : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he'
    rw [hF', Finset.coe_insert, Set.mem_insert_iff] at he'
    rcases he' with rfl | he'
    · exact hab
    · exact hFG (Finset.mem_of_mem_erase he')
  -- deleteEdges of linkGraph F is below linkGraph F'
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

end SSSCut474

open ShortestConnection.Principles in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e f : Sym2 V, e ∈ G.edgeSet → f ∈ G.edgeSet → w e = w f → e = f)
    (l : List (Sym2 V)) (hl : IsConstruction G w l) (F : Finset (Sym2 V)) (hF : IsSSS G w F) :
    ∀ e ∈ l, e ∈ F := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  rcases hl i hi with ⟨t, n, -, htn, he', hmin⟩ | ⟨u, n, -, hun, hGun, he', hmin⟩
  · rw [he']
    refine SSSCut474.cut_mem G w hw F hF {t} t n rfl ?_ htn ?_
    · intro h; exact htn.ne (Set.mem_singleton_iff.mp h).symm
    · intro x y hx _ hxy
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hmin y hxy
  · rw [he']
    refine SSSCut474.cut_mem G w hw F hF
      {x | (linkGraph (l.take i).toFinset).Reachable u x} u n
      (SimpleGraph.Reachable.refl _) hun hGun ?_
    intro x y hx hy hxy
    exact hmin x y hx hy hxy
