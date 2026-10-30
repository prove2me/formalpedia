-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanar_edge_count_upper_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:08:45.05051+00:00
-- url     : https://prove2.me/submissions/f128989f-6120-412d-977f-66be05f48673
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, hDrawing, hMaximal, hCardinality⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1 N hN
  have hBound := WilliamsonShmoys.maximal_planar_edge_bound__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1 H hDrawing hCard hMaximal
  omega