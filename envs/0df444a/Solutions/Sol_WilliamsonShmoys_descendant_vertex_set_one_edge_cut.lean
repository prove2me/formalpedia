-- Prove2me | solution 1 for WilliamsonShmoys.descendant_vertex_set_one_edge_cut
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:45:51.921132+00:00
-- url     : https://prove2.me/submissions/9bebe016-1e59-42de-bedc-c3c8f8bc6bb4

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace A3S56DF3

open SimpleGraph

lemma pu {W : Type} {G : SimpleGraph W} (hG : G.IsAcyclic) {a b : W} (p q : G.Walk a b)
    (hp : p.IsPath) (hq : q.IsPath) : p = q :=
  congrArg Subtype.val (hG.path_unique ⟨p, hp⟩ ⟨q, hq⟩)

lemma walkInd {W : Type} (G : SimpleGraph W) (S : Set W) {x y : W} (p : G.Walk x y)
    (hS : ∀ z ∈ p.support, z ∈ S) :
    (G.induce S).Reachable ⟨x, hS x p.start_mem_support⟩ ⟨y, hS y p.end_mem_support⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z y h p ih =>
    have hz : z ∈ S := hS z (by simp)
    refine Reachable.trans (Adj.reachable (?_ : (G.induce S).Adj ⟨x, _⟩ ⟨z, hz⟩))
      (ih (fun w hw => hS w (by simp [hw])))
    simpa using h

theorem main {V : Type} [Fintype V] (R : SimpleGraph V) (hR : R.IsTree)
    (root : V) (Q : (x : V) → R.Walk root x)
    (hQ : ∀ x, (Q x).IsPath) (v : V) :
    let S : Set V := {x | v ∈ (Q x).support}
    S.Nonempty ∧ (R.induce S).Connected ∧
      ∀ a b c d : V, R.Adj a b → a ∈ S → b ∉ S →
        R.Adj c d → c ∈ S → d ∉ S →
          (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  intro S
  have hac := hR.isAcyclic
  let D : V → Prop := fun x => v ∈ (Q x).support
  have hDv : D v := (Q v).end_mem_support
  have exitR : ∀ x y (h : R.Adj x y), D x → ¬ D y →
      x = v ∧ ∃ p : R.Walk root y, Q x = p.concat h.symm := by
    intro x y h hx hy
    by_cases hys : y ∈ (Q x).support
    · have e1 := (Q x).take_spec hys
      have e2 : (Q x).takeUntil y hys = Q y := pu hac _ _ ((hQ x).takeUntil hys) (hQ y)
      have e3 : (Q x).dropUntil y hys = Walk.cons h.symm Walk.nil :=
        pu hac _ _ ((hQ x).dropUntil hys) (by simp [h.ne.symm])
      rw [e2, e3, ← Walk.concat_eq_append] at e1
      refine ⟨?_, Q y, e1.symm⟩
      have hx' : v ∈ ((Q y).concat h.symm).support := by rw [e1]; exact hx
      rw [Walk.support_concat] at hx'
      simp only [List.mem_append, List.mem_singleton] at hx'
      rcases hx' with h1 | h1
      · exact absurd h1 hy
      · exact h1.symm
    · exfalso
      have e : (Q x).concat h = Q y := pu hac _ _ ((hQ x).concat hys h) (hQ y)
      apply hy
      show v ∈ (Q y).support
      rw [← e, Walk.support_concat]
      simp only [List.mem_append]
      exact Or.inl hx
  have parent : ∀ y y', R.Adj v y → R.Adj v y' → ¬ D y → ¬ D y' → y = y' := by
    intro y y' h h' hy hy'
    obtain ⟨-, p, hp⟩ := exitR v y h hDv hy
    obtain ⟨-, p', hp'⟩ := exitR v y' h' hDv hy'
    obtain ⟨hv, -⟩ := Walk.concat_inj (hp.symm.trans hp')
    exact hv
  have hreach : ∀ u (hu : u ∈ S), (R.induce S).Reachable ⟨v, hDv⟩ ⟨u, hu⟩ := by
    intro u hi
    obtain ⟨p, q, hpq⟩ : ∃ (p : R.Walk root v) (q : R.Walk v u),
        Q u = p.append q := ⟨_, _, ((Q _).take_spec hi).symm⟩
    have hqD : ∀ z ∈ q.support, z ∈ S := by
      intro z hz
      have e1 := q.take_spec hz
      have e2 : Q u = (p.append (q.takeUntil z hz)).append (q.dropUntil z hz) := by
        rw [← Walk.append_assoc, e1]; exact hpq
      have hpath : (p.append (q.takeUntil z hz)).IsPath := by
        have := hQ u; rw [e2] at this; exact this.of_append_left
      have e3 : p.append (q.takeUntil z hz) = Q z := pu hac _ _ hpath (hQ z)
      show v ∈ (Q z).support
      rw [← e3, Walk.mem_support_append_iff]
      exact Or.inl p.end_mem_support
    exact walkInd R S q hqD
  refine ⟨⟨v, hDv⟩, ?_, ?_⟩
  · rw [connected_iff]
    refine ⟨fun x y => ?_, ⟨⟨v, hDv⟩⟩⟩
    exact (hreach x.1 x.2).symm.trans (hreach y.1 y.2)
  · intro a b c d hab ha hb hcd hc hd
    obtain ⟨hav, -⟩ := exitR a b hab ha hb
    obtain ⟨hcv, -⟩ := exitR c d hcd hc hd
    subst hav hcv
    exact Or.inl ⟨rfl, parent _ _ hab hcd hb hd⟩

end A3S56DF3

theorem solution
    {V : Type} [Fintype V] (R : SimpleGraph V) (hR : R.IsTree)
    (root : V) (Q : (x : V) → R.Walk root x)
    (hQ : ∀ x, (Q x).IsPath) (v : V) :
    let S : Set V := {x | v ∈ (Q x).support}
    S.Nonempty ∧ (R.induce S).Connected ∧
      ∀ a b c d : V, R.Adj a b → a ∈ S → b ∉ S →
        R.Adj c d → c ∈ S → d ∉ S →
          (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  A3S56DF3.main R hR root Q hQ v

