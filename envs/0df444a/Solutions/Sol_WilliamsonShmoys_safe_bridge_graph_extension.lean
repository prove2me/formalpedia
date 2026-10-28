-- Prove2me | solution 1 for WilliamsonShmoys.safe_bridge_graph_extension
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:51.825333+00:00
-- url     : https://prove2.me/submissions/043cbde0-15bf-4a7b-b9e9-5ea7eb27017b

import Mathlib
import Definitions.Def_WilliamsonShmoys_HasSafeBridge
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hBridge : WilliamsonShmoys.HasSafeBridge G p arc) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      ∃ u v, H.Adj u v ∧ ¬ G.Reachable u v := by
  classical
  obtain ⟨u0, v0, huv, hnr, bridge, hb1, hb2, hb3, hb4, hb5, hb6⟩ := hBridge
  let H : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u0, v0)}
  have hHadj : ∀ a b, H.Adj a b ↔ G.Adj a b ∨ (a = u0 ∧ b = v0) ∨ (a = v0 ∧ b = u0) := by
    intro a b
    simp only [H, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact huv.ne
        · rw [h1, h2]; exact huv.ne'
  refine ⟨H, ?_, ?_, u0, v0, (hHadj _ _).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)), hnr⟩
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet] at he ⊢
      exact (hHadj _ _).2 (Or.inl he)
  · intro a b h
    rcases (hHadj _ _).1 h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · subst h1; subst h2; exact Or.inr hnr
    · subst h1; subst h2; exact Or.inr (fun hr => hnr hr.symm)
