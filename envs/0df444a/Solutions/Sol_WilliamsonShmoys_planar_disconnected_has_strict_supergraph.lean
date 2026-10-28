-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_strict_supergraph
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:38:00.026905+00:00
-- url     : https://prove2.me/submissions/a1095db6-1dfc-4032-a131-b438e541a61f

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
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  obtain ⟨K, hss, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP S181_hC
  rw [S181_eq K] at hss
  exact lt_irrefl _ hss
