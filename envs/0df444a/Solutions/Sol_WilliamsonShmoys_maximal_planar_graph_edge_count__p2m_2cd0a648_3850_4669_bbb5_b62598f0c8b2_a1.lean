-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:15:50.024602+00:00
-- url     : https://prove2.me/submissions/5caae3c5-d433-468e-bcb6-1493f90555d5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_edge_count_upper__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
    H hcard hplanar
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
    H hcard hplanar hmax
  omega
