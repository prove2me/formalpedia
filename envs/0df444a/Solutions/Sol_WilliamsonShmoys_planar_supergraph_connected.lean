-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_connected
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:43:50.072724+00:00
-- url     : https://prove2.me/submissions/16fad3b8-1aa0-42c6-ab90-6a0c160c7cf5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181_hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L),
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  intro h
  obtain ⟨H, -, hc, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP
  exact hc.nonempty.elim (fun v => v.elim)
