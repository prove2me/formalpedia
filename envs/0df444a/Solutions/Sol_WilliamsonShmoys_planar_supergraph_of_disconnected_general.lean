-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_of_disconnected_general
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:43:51.755498+00:00
-- url     : https://prove2.me/submissions/6ccc04cf-688c-440a-80af-333c9de7cd7c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hDisconnected : ¬ L.Connected), ∃ M : SimpleGraph V, L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M) := by
  intro h
  obtain ⟨M, -, hne, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
    (fun hc => hc.nonempty.elim fun a => a.elim0)
  exact hne (SimpleGraph.ext (funext fun a => a.elim0))
