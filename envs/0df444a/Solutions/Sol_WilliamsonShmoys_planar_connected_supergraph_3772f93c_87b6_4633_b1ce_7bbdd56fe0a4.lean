-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:13:28.91268+00:00
-- url     : https://prove2.me/submissions/10050806-242d-49ec-a175-2c3ea0bb63f9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys
theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K),
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  obtain ⟨H, -, -, hc⟩ := h (⊥ : SimpleGraph (Fin 0)) hd
  exact hc.nonempty.elim fun v => v.elim0
