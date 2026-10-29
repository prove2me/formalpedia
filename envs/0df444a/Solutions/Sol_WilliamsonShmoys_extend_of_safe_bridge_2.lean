-- Prove2me | solution 2 for WilliamsonShmoys.extend_of_safe_bridge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:43.546912+00:00
-- url     : https://prove2.me/submissions/9eb20af4-7560-4bfc-b343-f4c4a4c8c54f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_HasSafeBridge

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdgeDrawing : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧
      arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hNoCrossing : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hBridge : WilliamsonShmoys.HasSafeBridge G p arc) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) ∧
      ∃ arc' : V → V → ℝ → ℝ × ℝ,
        (∀ u v, u < v → G.Adj u v → arc' u v = arc u v) ∧
        (∀ u v, u < v → H.Adj u v →
          ContinuousOn (arc' u v) (Set.Icc 0 1) ∧
          Set.InjOn (arc' u v) (Set.Icc 0 1) ∧
          arc' u v 0 = p u ∧
          arc' u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc' u v t ≠ p w) ∧
        (∀ u v x y, u < v → x < y → H.Adj u v → H.Adj x y →
          (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            arc' u v t = arc' x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  classical
  obtain ⟨u, v, huv, hnr, bridge, hc, hi, h0, h1, hint, hcross⟩ := hBridge
  have hHadj : ∀ a b, (G ⊔ SimpleGraph.edge u v).Adj a b ↔
      G.Adj a b ∨ ((a = u ∧ b = v ∨ a = v ∧ b = u) ∧ a ≠ b) := fun a b => by
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  have hnew : ∀ a b, a < b → (G ⊔ SimpleGraph.edge u v).Adj a b → ¬ G.Adj a b →
      a = u ∧ b = v := by
    intro a b hab h hg
    rcases (hHadj a b).1 h with h | ⟨h | h, -⟩
    · exact absurd h hg
    · exact h
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd (hab.trans huv) (lt_irrefl _)
  have hold : ∀ a b, G.Adj a b → ¬ (a = u ∧ b = v) := by
    rintro a b h ⟨rfl, rfl⟩
    exact hnr h.reachable
  refine ⟨G ⊔ SimpleGraph.edge u v, SimpleGraph.edgeSet_subset_edgeSet.mpr le_sup_left, ?_,
    ⟨u, v, (hHadj u v).2 (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv.ne⟩), hnr⟩,
    fun a b => if a = u ∧ b = v then bridge else arc a b, ?_, ?_, ?_⟩
  · intro a b h
    rcases (hHadj a b).1 h with h | ⟨h | h, -⟩
    · exact Or.inl h
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr hnr
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr fun h' => hnr h'.symm
  · intro a b _ h
    dsimp only
    rw [if_neg (hold a b h)]
  · intro a b hab h
    dsimp only
    by_cases hg : G.Adj a b
    · rw [if_neg (hold a b hg)]
      exact hEdgeDrawing a b hab hg
    · obtain ⟨rfl, rfl⟩ := hnew a b hab h hg
      rw [if_pos ⟨rfl, rfl⟩]
      exact ⟨hc, hi, h0, h1, hint⟩
  · intro a b x y hab hxy h1' h2' hne t ht s hs heq
    dsimp only at heq
    by_cases hg1 : G.Adj a b <;> by_cases hg2 : G.Adj x y
    · rw [if_neg (hold a b hg1), if_neg (hold x y hg2)] at heq
      exact hNoCrossing a b x y hab hxy hg1 hg2 hne t ht s hs heq
    · obtain ⟨hx, hy⟩ := hnew x y hxy h2' hg2
      rw [if_neg (hold a b hg1), if_pos ⟨hx, hy⟩] at heq
      exact (hcross a b hab hg1 s hs t ht heq.symm).symm
    · obtain ⟨ha, hb⟩ := hnew a b hab h1' hg1
      rw [if_pos ⟨ha, hb⟩, if_neg (hold x y hg2)] at heq
      exact hcross x y hxy hg2 t ht s hs heq
    · obtain ⟨ha, hb⟩ := hnew a b hab h1' hg1
      obtain ⟨hx, hy⟩ := hnew x y hxy h2' hg2
      exact absurd (by rw [ha, hb, hx, hy]) hne
