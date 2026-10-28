-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_data_extend_free_arc_to_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:42:17.953655+00:00
-- url     : https://prove2.me/submissions/e2530534-ad45-47db-8a55-a2ed36bb780d

import Mathlib
import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
import Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

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
    (G H : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v : V)
    (hDrawing : WilliamsonShmoys.IsPlanarDrawingData G p arc)
    (hFree : WilliamsonShmoys.HasFreeConnectingArc G p arc u v)
    (hSub : G ≤ H) (hAdj : H.Adj u v)
    (hOnly : ∀ x y, H.Adj x y →
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact S181ext G H p arc u v hDrawing hFree hOnly
