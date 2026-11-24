-- Prove2me | solution 2 for WilliamsonShmoys.inclusion_maximal_planar_drawing_is_connected__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T04:55:41.565417+00:00
-- url     : https://prove2.me/submissions/4f552608-5bbe-477b-a1dd-439b1e6df9ab

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
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (M : SimpleGraph V)
      (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
      (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M),
      M.Connected) := by
  intro h
  exact not_conn0 _ (h (⊥ : SimpleGraph (Fin 0)) bot_draw0
    (fun N _ _ => by rw [eq_bot0 N]))
