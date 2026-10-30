-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_drawing_has_planar_extension__p2m_b968de7a_bb4e_4b2a_a58b_cf3030ff5cd1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:39.629011+00:00
-- url     : https://prove2.me/submissions/4b1f1248-c1b2-4a7c-8f19-349c3c82f5c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_edge_deficit__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ H := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
      H hplanar hV
  have hHcount :=
    WilliamsonShmoys.disconnected_planar_graph_has_strict_edge_deficit__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
      H hplanar hV hdisconnected
  have hneq : K ≠ H := by
    intro h
    subst K
    omega
  exact ⟨K, hHK, hKplanar, hneq⟩