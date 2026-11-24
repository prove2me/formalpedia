-- Prove2me | solution 1 for WilliamsonShmoys.planar_connect_components
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T04:55:43.239407+00:00
-- url     : https://prove2.me/submissions/0aeadc3f-2201-4e14-b227-969e584d056d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem bot_draw0 : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
  ⟨fun x => x.elim0, fun _ _ _ => 0, fun x => x.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem not_conn0 (G : SimpleGraph (Fin 0)) : ¬ G.Connected := fun hc => by
  obtain ⟨x⟩ := hc.nonempty
  exact x.elim0

theorem eq_bot0 (G : SimpleGraph (Fin 0)) : G = ⊥ := by
  ext x; exact x.elim0

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
      (hK : WilliamsonShmoys.HasPlanarDrawingOn K),
      ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  intro h
  obtain ⟨H, -, hH, -⟩ := h (⊥ : SimpleGraph (Fin 0)) bot_draw0
  exact not_conn0 _ hH
