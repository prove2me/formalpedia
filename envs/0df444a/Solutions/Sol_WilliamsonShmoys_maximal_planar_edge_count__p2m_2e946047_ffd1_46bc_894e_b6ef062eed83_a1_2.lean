-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:23:55.068754+00:00
-- url     : https://prove2.me/submissions/85590b69-8c56-4c5a-a7c9-e997ab078546

import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57 M hM hV hmax
