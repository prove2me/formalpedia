-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_strict_supergraph_step
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:38:01.814945+00:00
-- url     : https://prove2.me/submissions/c378d348-86a4-48f6-833c-c33bf840ac4f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181_hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩

theorem S181_hC : ¬ (⊥ : SimpleGraph Empty).Connected := fun hc => hc.nonempty.elim (fun v => v.elim)

theorem S181_eq (K : SimpleGraph Empty) : K = ⊥ := by
  ext a; exact a.elim

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V),
    WilliamsonShmoys.HasPlanarDrawingOn G →
    ¬ G.Connected →
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard < H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  obtain ⟨L, -, hlt, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP S181_hC
  rw [S181_eq L] at hlt
  exact lt_irrefl _ hlt
