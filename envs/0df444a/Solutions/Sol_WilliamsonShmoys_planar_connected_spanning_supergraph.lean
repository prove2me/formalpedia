-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_spanning_supergraph
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:38:10.060473+00:00
-- url     : https://prove2.me/submissions/7d5b6cf3-2976-4b87-b17b-d1e47892b522

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G),
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun hc => hc.nonempty.elim fun v => v.elim0
  obtain ⟨H, -, hH, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hd
  exact hH.nonempty.elim fun v => v.elim0
