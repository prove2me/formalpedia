-- Prove2me | solution 1 for SupplyChainTheory.euler_tour_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T21:07:54.753243+00:00
-- url     : https://prove2.me/submissions/62d4f86a-8761-436d-aea5-883e6d5b3d66

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

/-- If every edge at `x` lies on the trail `p`, then the trail has `deg x` edges at `x`. -/
private lemma countP_eq_degree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u w : V} (p : G.Walk u w) (hp : p.IsTrail) (x : V)
    (hall : ∀ y, G.Adj x y → s(x, y) ∈ p.edges) :
    p.edges.countP (fun e => x ∈ e) = G.degree x := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hp.edges_nodup.filter _)]
  congr 1
  ext e
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, SimpleGraph.mem_incidenceFinset,
    SimpleGraph.incidenceSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨he, hx⟩; exact ⟨p.edges_subset_edgeSet he, hx⟩
  · rintro ⟨he, hx⟩
    refine ⟨?_, hx⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hall b he
      · rw [Sym2.eq_swap]; exact hall a he.symm

/-- A trail with distinct ends can leave its end along an unused edge (all degrees even). -/
private lemma exists_unused_at_end {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, Even (G.degree v)) {u w : V} (p : G.Walk u w) (hp : p.IsTrail) (huw : u ≠ w) :
    ∃ y, G.Adj w y ∧ s(w, y) ∉ p.edges := by
  by_contra hno
  push Not at hno
  have hodd : ¬ Even (p.edges.countP (fun e => w ∈ e)) := by
    rw [hp.even_countP_edges_iff w]; intro h; exact (h huw).2 rfl
  exact hodd (countP_eq_degree G p hp w hno ▸ hdeg w)

/-- Walking from the support of `p` to a vertex with an edge unused by `p`, the first unused
edge along the way starts on the support of `p`. -/
private lemma exists_unused_along {V : Type*} (G : SimpleGraph V) {u : V} (p : G.Walk u u) :
    ∀ {x c : V} (r : G.Walk x c), x ∈ p.support → (∃ d, G.Adj c d ∧ s(c, d) ∉ p.edges) →
      ∃ x y, x ∈ p.support ∧ G.Adj x y ∧ s(x, y) ∉ p.edges := by
  intro x c r
  induction r with
  | nil => rintro hx ⟨d, hd, hdp⟩; exact ⟨_, d, hx, hd, hdp⟩
  | @cons x' z c' h _r ih =>
    intro hx hend
    by_cases hz : s(x', z) ∈ p.edges
    · exact ih (p.snd_mem_support_of_mem_edges hz) hend
    · exact ⟨x', z, hx, h, hz⟩

/-- If a closed walk misses some edge of a connected graph, it misses an edge at one of its
vertices. -/
private lemma exists_unused_at_support {V : Type*} (G : SimpleGraph V) (hG : G.Connected) {u : V}
    (p : G.Walk u u) {a b : V} (hab : G.Adj a b) (habp : s(a, b) ∉ p.edges) :
    ∃ x y, x ∈ p.support ∧ G.Adj x y ∧ s(x, y) ∉ p.edges := by
  obtain ⟨r⟩ := hG.preconnected u a
  exact exists_unused_along G p r p.start_mem_support ⟨b, hab, habp⟩

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) :
    (∀ v, Even (G.degree v)) ↔ ∃ (v : V) (p : G.Walk v v), p.IsEulerian := by
  constructor
  swap
  · -- An Eulerian circuit meets every vertex in an even number of edges.
    rintro ⟨v, p, hp⟩ x
    exact (hp.even_degree_iff).mpr (fun h => absurd rfl h)
  intro hdeg
  -- Take a longest trail.
  let P : ℕ → Prop := fun k => ∃ (u w : V) (p : G.Walk u w), p.IsTrail ∧ p.length = k
  have hP0 : P 0 := by
    obtain ⟨v⟩ := hG.nonempty
    exact ⟨v, v, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsTrail.nil, rfl⟩
  have hbound : ∀ k, P k → k ≤ G.edgeFinset.card := by
    rintro k ⟨u, w, p, hp, rfl⟩; exact hp.length_le_card_edgeFinset
  set N := Nat.findGreatest P G.edgeFinset.card with hN
  have hPN : P N := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ k, P k → k ≤ N := fun k hk => Nat.le_findGreatest (hbound k hk) hk
  obtain ⟨u, w, p, hp, hlen⟩ := hPN
  -- A longest trail is closed: otherwise it could be extended at its end.
  by_cases huw : u = w
  swap
  · exfalso
    obtain ⟨y, hwy, hunused⟩ := exists_unused_at_end G hdeg p hp huw
    have hq : (SimpleGraph.Walk.cons hwy.symm p.reverse).IsTrail := by
      rw [SimpleGraph.Walk.isTrail_cons, SimpleGraph.Walk.edges_reverse, List.mem_reverse,
        Sym2.eq_swap]
      exact ⟨hp.reverse, hunused⟩
    have := hmax _ ⟨_, _, _, hq, rfl⟩
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse] at this
    omega
  subst huw
  refine ⟨u, p, (SimpleGraph.Walk.isEulerian_iff p).mpr ⟨hp, ?_⟩⟩
  -- A longest closed trail uses every edge: otherwise rotate it to a vertex with an unused
  -- edge and extend.
  intro e he
  by_contra hne
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨x, y, hx, hxy, hunused⟩ := exists_unused_at_support G hG p he hne
    set q := p.rotate x hx with hqdef
    have hqT : q.IsTrail := hp.rotate hx
    have hqE : s(x, y) ∉ q.edges := fun h =>
      hunused ((p.rotate_edges x hx).mem_iff.mp h)
    have hq' : (SimpleGraph.Walk.cons hxy.symm q).IsTrail := by
      rw [SimpleGraph.Walk.isTrail_cons, Sym2.eq_swap]
      exact ⟨hqT, hqE⟩
    have := hmax _ ⟨_, _, _, hq', rfl⟩
    simp only [SimpleGraph.Walk.length_cons, hqdef, SimpleGraph.Walk.length_rotate] at this
    omega
