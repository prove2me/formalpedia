-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:44:55.792077+00:00
-- url     : https://prove2.me/submissions/2a13c58c-2da7-4531-b64f-4d7662da0b60

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected),
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  obtain ⟨L, -, hne, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hd (fun hc => hc.nonempty.elim fun v => v.elim0)
  apply hne
  ext u
  exact u.elim0
