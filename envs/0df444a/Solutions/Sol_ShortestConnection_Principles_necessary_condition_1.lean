-- Prove2me | solution 1 for ShortestConnection.Principles.necessary_condition_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:06:26.051156+00:00
-- url     : https://prove2.me/submissions/980a3f5d-befc-4775-bd65-21c4ed11f8ec

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

theorem aux_nc1_edgeSet {V : Type*} (H : Finset (Sym2 V)) (hH : ∀ e ∈ H, ¬ e.IsDiag) :
    (linkGraph H).edgeSet = (H : Set (Sym2 V)) := by
  unfold linkGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · intro he
    exact he.1
  · intro he
    exact ⟨he, hH e he⟩

theorem aux_nc1_card {V : Type*} (H : Finset (Sym2 V)) (hH : ∀ e ∈ H, ¬ e.IsDiag) :
    Nat.card (linkGraph H).edgeSet = H.card := by
  rw [aux_nc1_edgeSet H hH, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem aux_nc1_adj {V : Type*} (H : Finset (Sym2 V)) (u v : V) :
    (linkGraph H).Adj u v ↔ s(u, v) ∈ H ∧ u ≠ v := by
  unfold linkGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  simp

end ShortestConnection.Principles

open ShortestConnection.Principles

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hF : IsSSS G w F) (t : V) :
    ∃ n : V, G.Adj t n ∧ s(t, n) ∈ F ∧ ∀ m : V, G.Adj t m → w s(t, n) ≤ w s(t, m) := by
  classical
  have hsub : (F : Set (Sym2 V)) ⊆ G.edgeSet := hF.1.1
  have htree : (linkGraph F).IsTree := hF.1.2
  -- a nearest neighbour m0 of t
  set S : Finset V := Finset.univ.filter (fun m => G.Adj t m) with hS
  have hSne : S.Nonempty := by
    obtain ⟨u, hu⟩ := exists_ne t
    obtain ⟨p⟩ := hG.preconnected t u
    cases p with
    | nil => exact absurd rfl hu
    | cons h _ => exact ⟨_, by simpa [hS] using h⟩
  obtain ⟨m0, hm0S, hm0min⟩ := S.exists_min_image (fun m => w s(t, m)) hSne
  have hm0 : G.Adj t m0 := by simpa [hS] using hm0S
  have hmin : ∀ m : V, G.Adj t m → w s(t, m0) ≤ w s(t, m) := by
    intro m hm
    exact hm0min m (by simp [hS, hm])
  by_cases hin : s(t, m0) ∈ F
  · exact ⟨m0, hm0, hin, hmin⟩
  have hne : t ≠ m0 := hm0.ne
  -- the first edge of the tree path from t to m0
  have key : ∀ q : (linkGraph F).Walk t m0, q.IsPath →
      ∃ x, (linkGraph F).Adj t x ∧ ∃ r : (linkGraph F).Walk x m0, t ∉ r.support := by
    intro q hq
    cases q with
    | nil => exact absurd rfl hne
    | cons h r => exact ⟨_, h, r, ((SimpleGraph.Walk.cons_isPath_iff h r).1 hq).2⟩
  obtain ⟨p⟩ := htree.1.preconnected t m0
  obtain ⟨x, hx, r, hr⟩ := key p.bypass p.bypass_isPath
  have hxF : s(t, x) ∈ F := ((aux_nc1_adj F t x).1 hx).1
  have hxG : G.Adj t x := hsub hxF
  -- the exchanged tree
  set F' : Finset (Sym2 V) := insert s(t, m0) (F.erase s(t, x)) with hF'
  have hnotin : s(t, m0) ∉ F.erase s(t, x) := fun h => hin (Finset.mem_of_mem_erase h)
  have hnodiagF : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact G.not_isDiag_of_mem_edgeSet (hsub he)
  have hsub' : (F' : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    have he' : e = s(t, m0) ∨ e ∈ F.erase s(t, x) := Finset.mem_insert.1 he
    rcases he' with rfl | he'
    · exact hm0
    · exact hsub (Finset.mem_of_mem_erase he')
  have hnodiagF' : ∀ e ∈ F', ¬ e.IsDiag := by
    intro e he
    exact G.not_isDiag_of_mem_edgeSet (hsub' he)
  have hm0F' : (linkGraph F').Adj t m0 := by
    rw [aux_nc1_adj]
    exact ⟨Finset.mem_insert_self _ _, hne⟩
  -- t and x are joined in F'
  have htx : (linkGraph F').Reachable x t := by
    have hr' : ∀ e ∈ r.edges, e ∈ (linkGraph F').edgeSet := by
      intro e he
      have heF : e ∈ (linkGraph F).edgeSet := SimpleGraph.Walk.edges_subset_edgeSet r he
      rw [aux_nc1_edgeSet F hnodiagF] at heF
      rw [aux_nc1_edgeSet F' hnodiagF']
      have hne' : e ≠ s(t, x) := by
        rintro rfl
        exact hr (SimpleGraph.Walk.fst_mem_support_of_mem_edges r he)
      exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hne', heF⟩)
    exact ⟨(r.transfer (linkGraph F') hr').append (SimpleGraph.Walk.cons hm0F'.symm .nil)⟩
  have hadjR : ∀ a b : V, (linkGraph F).Adj a b → (linkGraph F').Reachable a b := by
    intro a b hab
    rw [aux_nc1_adj] at hab
    by_cases heq : s(a, b) = s(t, x)
    · rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact htx.symm
      · exact htx
    · apply SimpleGraph.Adj.reachable
      rw [aux_nc1_adj]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨heq, hab.1⟩), hab.2⟩
  have hreach : ∀ a b : V, (linkGraph F).Reachable a b → (linkGraph F').Reachable a b := by
    intro a b ⟨q⟩
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h _ ih => exact (hadjR _ _ h).trans ih
  have hconn : (linkGraph F').Connected := by
    have : Nonempty V := hG.nonempty
    exact ⟨fun a b => hreach a b (htree.1.preconnected a b)⟩
  have hcardF := (SimpleGraph.isTree_iff_connected_and_card.1 htree).2
  rw [aux_nc1_card F hnodiagF] at hcardF
  have hcardF' : F'.card = F.card := by
    rw [hF', Finset.card_insert_of_notMem hnotin, Finset.card_erase_add_one hxF]
  have htree' : (linkGraph F').IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [aux_nc1_card F' hnodiagF', hcardF']
    exact hcardF
  have hSST : IsSpanningSubtree G F' := ⟨hsub', htree'⟩
  have hlen := hF.2 F' hSST
  have hlenF' : length w F' = w s(t, m0) + (length w F - w s(t, x)) := by
    unfold length
    rw [hF', Finset.sum_insert hnotin, ← Finset.add_sum_erase F w hxF]
    ring
  rw [hlenF'] at hlen
  have hle : w s(t, x) ≤ w s(t, m0) := by linarith
  exact ⟨x, hxG, hxF, fun m hm => hle.trans (hmin m hm)⟩
