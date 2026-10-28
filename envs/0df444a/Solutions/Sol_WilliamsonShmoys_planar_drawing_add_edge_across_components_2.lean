-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_add_edge_across_components
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:38:03.489273+00:00
-- url     : https://prove2.me/submissions/7fa1c299-fdb4-4016-bbb8-92a49b1d1624

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
    ∃ u v : V, ¬ G.Adj u v ∧
      ∃ H : SimpleGraph V,
        G ≤ H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  obtain ⟨u, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP S181_hC
  exact u.elim
