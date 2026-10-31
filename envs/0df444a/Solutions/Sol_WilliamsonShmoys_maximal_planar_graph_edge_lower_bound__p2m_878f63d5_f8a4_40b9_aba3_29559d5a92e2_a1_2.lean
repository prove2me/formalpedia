-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:17:48.045082+00:00
-- url     : https://prove2.me/submissions/767bae0a-5fdf-4cc8-b185-aa5c8a9aa245

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1 M hM hV hMax
