-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_local_step__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:46:13.752211+00:00
-- url     : https://prove2.me/submissions/744c9be6-571d-4db1-a280-c8935c39062b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected),
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun hc => hc.nonempty.elim fun v => v.elim0
  obtain ⟨H, -, hH, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hd hnc
  exact hH (SimpleGraph.ext (funext fun u => u.elim0))
