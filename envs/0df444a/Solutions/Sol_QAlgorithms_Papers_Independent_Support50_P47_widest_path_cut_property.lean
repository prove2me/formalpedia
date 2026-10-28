-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P47.widest_path_cut_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:15:17.929749+00:00
-- url     : https://prove2.me/submissions/395a532e-b3e9-499e-aac6-a5a9aa5761b2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P47

open QAlgorithms.Papers.Independent.Support50.P47

namespace S167A

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

lemma routeWeight_mem (G : WeightedNetwork V E) {a b : V} (p : Route G a b) :
    ∃ i : Fin p.length, routeWeight G p = G.weight (p.edge i) := by
  haveI : Nonempty (Fin p.length) := ⟨⟨0, p.positive⟩⟩
  have := (Set.range_nonempty (fun i : Fin p.length => G.weight (p.edge i))).csInf_mem
    (Set.toFinite _)
  obtain ⟨i, hi⟩ := this
  exact ⟨i, by simp only [routeWeight]; exact hi.symm⟩

lemma routeWeight_le (G : WeightedNetwork V E) {a b : V} (p : Route G a b) (i : Fin p.length) :
    routeWeight G p ≤ G.weight (p.edge i) :=
  csInf_le (Set.toFinite _).bddBelow ⟨i, rfl⟩

lemma cut_bdd (G : WeightedNetwork V E) (A : Set V) :
    BddAbove {w : ℝ | ∃ e : E,
      ((G.left e ∈ A ∧ G.right e ∉ A) ∨ (G.right e ∈ A ∧ G.left e ∉ A)) ∧ w = G.weight e} :=
  ((Set.toFinite (Set.range G.weight)).subset (by rintro w ⟨e, -, rfl⟩; exact ⟨e, rfl⟩)).bddAbove

/-- every route crosses every separating set -/
lemma route_crosses (G : WeightedNetwork V E) {a b : V} (p : Route G a b) (B : Set V)
    (ha : a ∈ B) (hb : b ∉ B) :
    ∃ i : Fin p.length, p.vertex i.castSucc ∈ B ∧ p.vertex i.succ ∉ B := by
  by_contra h
  push_neg at h
  have : ∀ k : ℕ, (hk : k ≤ p.length) → p.vertex ⟨k, by omega⟩ ∈ B := by
    intro k
    induction k with
    | zero => intro _; rw [p.start]; exact ha
    | succ k ih =>
      intro hk
      exact h ⟨k, by omega⟩ (ih (by omega))
  have := this p.length le_rfl
  rw [show (⟨p.length, by omega⟩ : Fin (p.length + 1)) = Fin.last _ from rfl, p.finish] at this
  exact hb this

lemma le_cutWeight (G : WeightedNetwork V E) {a b : V} (p : Route G a b) (B : Set V)
    (ha : a ∈ B) (hb : b ∉ B) : routeWeight G p ≤ cutWeight G B := by
  obtain ⟨i, hi1, hi2⟩ := route_crosses G p B ha hb
  refine (routeWeight_le G p i).trans (le_csSup (cut_bdd G B) ⟨p.edge i, ?_, rfl⟩)
  rcases p.follows i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [h1, h2]; exact ⟨hi1, hi2⟩
  · right; rw [h1, h2]; exact ⟨hi1, hi2⟩

/-- the graph of edges with weight > t -/
def H (G : WeightedNetwork V E) (t : ℝ) : SimpleGraph V where
  Adj u w := u ≠ w ∧ ∃ e, t < G.weight e ∧
    ((G.left e = u ∧ G.right e = w) ∨ (G.right e = u ∧ G.left e = w))
  symm := ⟨by
    rintro u w ⟨h, e, he, h'⟩
    exact ⟨h.symm, e, he, by tauto⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

lemma route_of_reach (G : WeightedNetwork V E) (t : ℝ) {a b : V} (hab : a ≠ b)
    (h : (H G t).Reachable a b) : ∃ q : Route G a b, t < routeWeight G q := by
  classical
  obtain ⟨w⟩ := h
  let P := w.toPath
  have hP : P.1.IsPath := P.2
  have hlen : 0 < P.1.length := by
    rcases Nat.eq_zero_or_pos P.1.length with h0 | h0
    · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hab
    · exact h0
  have hadj : ∀ i : Fin P.1.length, (H G t).Adj (P.1.getVert i) (P.1.getVert (i + 1)) :=
    fun i => P.1.adj_getVert_succ i.2
  let q : Route G a b :=
    { length := P.1.length
      positive := hlen
      vertex := fun i => P.1.getVert i
      edge := fun i => (hadj i).2.choose
      start := by simp
      finish := by simp
      simple := by
        intro i j hij
        exact Fin.ext (hP.getVert_injOn (by simp; omega) (by simp; omega) hij)
      follows := fun i => by
        simpa using (hadj i).2.choose_spec.2 }
  refine ⟨q, ?_⟩
  obtain ⟨i, hi⟩ := routeWeight_mem G q
  rw [hi]
  exact (hadj i).2.choose_spec.1

theorem main (G : WeightedNetwork V E)
    (hconn : IsConnected G) (a b : V) (hab : a ≠ b) :
    ∃ p : Route G a b, ∃ A : Set V,
      a ∈ A ∧ b ∉ A ∧ routeWeight G p = cutWeight G A ∧
      (∀ q : Route G a b, routeWeight G q ≤ routeWeight G p) ∧
      (∀ B : Set V, a ∈ B → b ∉ B → cutWeight G A ≤ cutWeight G B) := by
  classical
  set S := Set.range (routeWeight G : Route G a b → ℝ) with hS
  have hSfin : S.Finite := (Set.toFinite (Set.range G.weight)).subset (by
    rintro x ⟨q, rfl⟩
    obtain ⟨i, hi⟩ := routeWeight_mem G q
    exact ⟨_, hi.symm⟩)
  have hSne : S.Nonempty := by
    obtain ⟨q⟩ := hconn a b hab
    exact ⟨_, q, rfl⟩
  obtain ⟨p, hp⟩ := hSne.csSup_mem hSfin
  have hmax : ∀ q : Route G a b, routeWeight G q ≤ routeWeight G p := fun q => by
    rw [hp]; exact le_csSup hSfin.bddAbove ⟨q, rfl⟩
  set t := routeWeight G p
  let A : Set V := {x | (H G t).Reachable a x}
  have haA : a ∈ A := SimpleGraph.Reachable.refl a
  have hbA : b ∉ A := by
    intro hb
    obtain ⟨q, hq⟩ := route_of_reach G t hab hb
    exact absurd (hmax q) (not_le.2 hq)
  have hcut : cutWeight G A ≤ t := by
    apply csSup_le
    · obtain ⟨q⟩ := hconn a b hab
      obtain ⟨i, hi1, hi2⟩ := route_crosses G q A haA hbA
      refine ⟨_, q.edge i, ?_, rfl⟩
      rcases q.follows i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1, h2]; exact ⟨hi1, hi2⟩
      · right; rw [h1, h2]; exact ⟨hi1, hi2⟩
    · rintro w ⟨e, he, rfl⟩
      by_contra hlt
      push_neg at hlt
      have hsep := G.separated e
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (SimpleGraph.Reachable.trans h1
          (SimpleGraph.Adj.reachable ⟨hsep, e, hlt, Or.inl ⟨rfl, rfl⟩⟩))
      · exact h2 (SimpleGraph.Reachable.trans h1
          (SimpleGraph.Adj.reachable ⟨hsep.symm, e, hlt, Or.inr ⟨rfl, rfl⟩⟩))
  have heq : t = cutWeight G A := le_antisymm (le_cutWeight G p A haA hbA) hcut
  refine ⟨p, A, haA, hbA, heq, hmax, fun B hB1 hB2 => ?_⟩
  rw [← heq]
  exact le_cutWeight G p B hB1 hB2

end S167A

universe u v

theorem solution {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] (G : WeightedNetwork V E)
    (hconn : IsConnected G) (a b : V) (hab : a ≠ b) :
    ∃ p : Route G a b, ∃ A : Set V,
      a ∈ A ∧ b ∉ A ∧ routeWeight G p = cutWeight G A ∧
      (∀ q : Route G a b, routeWeight G q ≤ routeWeight G p) ∧
      (∀ B : Set V, a ∈ B → b ∉ B → cutWeight G A ≤ cutWeight G B) :=
  S167A.main G hconn a b hab
