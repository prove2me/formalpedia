-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:15:16.042232+00:00
-- url     : https://prove2.me/submissions/4ab406bc-5044-4a71-a0a5-2adc89e6cb6c

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_d831683a_dc67_4372_b92f_31061460229f_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_d831683a_dc67_4372_b92f_31061460229f_a2 M hplanar hcard hmax
