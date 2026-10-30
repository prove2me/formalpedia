-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_of_disconnected__p2m_008dc069_b8e6_4096_b412_eae96eda23f6_a1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:33:41.724423+00:00
-- url     : https://prove2.me/submissions/86efaf57-d172-45b9-84c4-b7f784f689a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hNotConnected : ¬ K.Connected),
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ¬ L ≤ K) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun hc => hc.nonempty.elim fun v => v.elim0
  obtain ⟨L, -, -, hL⟩ := h (⊥ : SimpleGraph (Fin 0)) hd hnc
  exact hL fun u => u.elim0
