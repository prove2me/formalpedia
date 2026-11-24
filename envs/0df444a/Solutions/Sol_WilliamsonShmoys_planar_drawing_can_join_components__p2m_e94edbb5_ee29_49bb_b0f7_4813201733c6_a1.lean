-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_can_join_components__p2m_e94edbb5_ee29_49bb_b0f7_4813201733c6_a1
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T04:55:43.876315+00:00
-- url     : https://prove2.me/submissions/6eda1f87-50b6-4000-8487-8c010b2cb0a0

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
      (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hDisc : ¬ H.Connected),
      ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K ≤ H) := by
  intro h
  obtain ⟨K, -, -, hK⟩ := h (⊥ : SimpleGraph (Fin 0)) bot_draw0 (not_conn0 _)
  exact hK (by rw [eq_bot0 K])
