-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_extend_free_arc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:42:20.181544+00:00
-- url     : https://prove2.me/submissions/6b1e9c32-7eb7-4e44-ac63-10e666eb006c

import Mathlib
import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
import Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc

set_option autoImplicit false

theorem S181ext {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v : V)
    (hDrawing : WilliamsonShmoys.IsPlanarDrawingData G p arc)
    (hFree : WilliamsonShmoys.HasFreeConnectingArc G p arc u v)
    (hOnly : ∀ x y, H.Adj x y →
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  obtain ⟨hp, h1, h2⟩ := hDrawing
  obtain ⟨huv, γ, g1, g2, g3, g4, g5, g6⟩ := hFree
  have key : ∀ x y, x < y → H.Adj x y →
      (x = u ∧ y = v) ∨ (¬ (x = u ∧ y = v) ∧ G.Adj x y) := by
    intro x y hxy hH
    by_cases h : x = u ∧ y = v
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rcases hOnly x y hH with h' | h' | ⟨rfl, rfl⟩
      · exact h'
      · exact (h h').elim
      · exact (lt_asymm hxy huv).elim
  refine ⟨p, fun x y => if x = u ∧ y = v then γ else arc x y, hp,
    fun x y hxy hH => ?_, fun x y a b hxy hab hH1 hH2 hne t ht s hs heq => ?_⟩
  · rcases key x y hxy hH with h | ⟨hn, hG⟩
    · simp only [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨g1, g2, g3, g4, g5⟩
    · simp only [if_neg hn]
      exact h1 x y hxy hG
  · rcases key x y hxy hH1 with h | ⟨hn, hG⟩ <;> rcases key a b hab hH2 with h' | ⟨hn', hG'⟩
    · exact (hne (by rw [h.1, h.2, h'.1, h'.2])).elim
    · simp only [if_pos h, if_neg hn'] at heq
      exact g6 a b hab hG' t ht s hs heq
    · simp only [if_pos h', if_neg hn] at heq
      exact (g6 x y hxy hG s hs t ht heq.symm).symm
    · simp only [if_neg hn, if_neg hn'] at heq
      exact h2 x y a b hxy hab hG hG' hne t ht s hs heq

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hDrawing : WilliamsonShmoys.IsPlanarDrawingData G p arc)
    (u v : V) (hNotAdj : ¬ G.Adj u v)
    (hFree : WilliamsonShmoys.HasFreeConnectingArc G p arc u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  have huv : u ≠ v := ne_of_lt hFree.1
  refine ⟨G ⊔ SimpleGraph.edge u v, le_sup_left, ?_, ?_⟩
  · simp [SimpleGraph.edge_adj, huv]
  · refine S181ext G _ p arc u v hDrawing hFree (fun x y h => ?_)
    simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at h
    tauto
