-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T04:55:42.457574+00:00
-- url     : https://prove2.me/submissions/bb828dca-5c20-4992-8022-45a822bec65e

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
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
      (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
      (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H),
      H.Connected) := by
  intro h
  exact not_conn0 _ (h (⊥ : SimpleGraph (Fin 0)) bot_draw0
    (fun N _ _ => by rw [eq_bot0 N]))
