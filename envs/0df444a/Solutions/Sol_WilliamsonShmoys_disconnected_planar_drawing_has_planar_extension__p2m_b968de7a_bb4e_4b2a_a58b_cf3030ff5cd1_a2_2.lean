-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_drawing_has_planar_extension__p2m_b968de7a_bb4e_4b2a_a58b_cf3030ff5cd1_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:24:13.791727+00:00
-- url     : https://prove2.me/submissions/aff94e3f-ee6d-4b27-bca0-89d20451d23b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ H := by
  obtain ⟨J, hHJ, hne, hJ⟩ :=
    WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing H hplanar hV hdisconnected
  exact ⟨J, hHJ, hJ, hne⟩
