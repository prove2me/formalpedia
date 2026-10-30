-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_f15616f1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:31:57.456999+00:00
-- url     : https://prove2.me/submissions/6b556e1a-cf8e-483f-9fdd-a3092777f8fb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_large__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a4
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_edge_count_upper_bound__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨G, _hHG, hConnected, hDrawing, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_large__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a4
      H hH hCard
  have hBound :=
    WilliamsonShmoys.connected_planar_simple_graph_edge_count_upper_bound__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2
      G hDrawing hConnected hCard
  omega
