-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_one_step_merge
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:20:26.877995+00:00
-- url     : https://prove2.me/submissions/146a7127-c9aa-4c7c-8650-25a4c6779730

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181_hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩

theorem S181_hC : ¬ (⊥ : SimpleGraph Empty).Connected := fun hc => hc.nonempty.elim (fun v => v.elim)

theorem S181_eq (K : SimpleGraph Empty) : K = ⊥ := by
  ext a; exact a.elim

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected),
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) := by
  intro h
  obtain ⟨H, hlt, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP S181_hC
  rw [S181_eq H] at hlt
  exact lt_irrefl _ hlt
