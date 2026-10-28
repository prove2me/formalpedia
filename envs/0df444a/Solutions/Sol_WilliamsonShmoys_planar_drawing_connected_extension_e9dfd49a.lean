-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_e9dfd49a
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:15:35.841457+00:00
-- url     : https://prove2.me/submissions/85465507-fd4c-4586-b984-61de7a7a1ddc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G),
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int)) := by
  intro h
  obtain ⟨H, -, -, hc, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
  exact hc.nonempty.elim fun a => a.elim0
