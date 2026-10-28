-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_adds_an_edge_between_components
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:28:05.60071+00:00
-- url     : https://prove2.me/submissions/9942183a-8d62-4bc1-aa91-d313712b8f33

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181_hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩

theorem S181_hC : ¬ (⊥ : SimpleGraph Empty).Connected := fun hc => hc.nonempty.elim (fun v => v.elim)

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hDisconnected : ¬ P.Connected),
    ∃ u v : V, u ≠ v ∧ ¬ P.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn
        (P ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V)))) := by
  intro h
  obtain ⟨u, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP S181_hC
  exact u.elim
