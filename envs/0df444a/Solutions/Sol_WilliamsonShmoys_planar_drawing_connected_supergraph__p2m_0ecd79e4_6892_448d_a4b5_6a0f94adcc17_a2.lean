-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_0ecd79e4_6892_448d_a4b5_6a0f94adcc17_a2
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T04:52:27.023283+00:00
-- url     : https://prove2.me/submissions/394b9250-1c67-4684-ad0a-934ce884a16d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (J : SimpleGraph V)
      (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J),
      ∃ K : SimpleGraph V,
        J ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
          J.edgeSet.ncard ≤ K.edgeSet.ncard) := by
  intro h
  have hDraw : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun x => x.elim0, fun _ _ _ => 0, fun x => x.elim0,
      fun u => u.elim0, fun u => u.elim0⟩
  obtain ⟨K, -, hK, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hDraw
  obtain ⟨x⟩ := hK.nonempty
  exact x.elim0
