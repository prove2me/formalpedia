-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_0e98e963_983c_4fb9_9e38_7bdda2495dff_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:23:10.51036+00:00
-- url     : https://prove2.me/submissions/1871dc32-4bd4-4383-b5c2-3c31f344e09d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_from_euler__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_connected_induced_subgraphs__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induced__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  apply WilliamsonShmoys.edge_bound_from_connected_induced_subgraphs__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1 G hV
  intro S hS hConn
  have hBound :=
    WilliamsonShmoys.connected_planar_edge_bound_from_euler__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
      (G.induce (S : Set V)) hConn (by simpa using hS)
      (WilliamsonShmoys.planar_drawing_induced__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1 G hG S)
  simpa using hBound