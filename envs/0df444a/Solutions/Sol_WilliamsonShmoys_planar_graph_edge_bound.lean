-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:27:01.087508+00:00
-- url     : https://prove2.me/submissions/18f11b33-ea5d-48a6-a0b8-39107c29a37f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (M : SimpleGraph V),
      3 ≤ Fintype.card V →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 3)) := by
    refine ⟨fun i => (((i : ℕ) : ℝ), (0 : ℝ)), fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro a b hab
      simp only [Prod.mk.injEq, and_true, Nat.cast_inj] at hab
      exact Fin.ext hab
    · intro u v _ huv; exact absurd huv (by simp)
    · intro u v x y _ _ huv; exact absurd huv (by simp)
  have := h (⊥ : SimpleGraph (Fin 3)) (by simp) hd
  simp at this
