-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:11:02.228313+00:00
-- url     : https://prove2.me/submissions/4b799e9e-a09c-44f4-8116-ffa2c8e26a13

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_2907dc87_c05a_4d84_a687_2b7bae17f05a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_2907dc87_c05a_4d84_a687_2b7bae17f05a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hEdgeCount, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_2907dc87_c05a_4d84_a687_2b7bae17f05a G hG
  have hHcard :=
    WilliamsonShmoys.maximal_planar_edge_count_2907dc87_c05a_4d84_a687_2b7bae17f05a H hH hV hMax
  calc
    G.edgeSet.ncard ≤ H.edgeSet.ncard := hEdgeCount
    _ = 3 * Fintype.card V - 6 := hHcard