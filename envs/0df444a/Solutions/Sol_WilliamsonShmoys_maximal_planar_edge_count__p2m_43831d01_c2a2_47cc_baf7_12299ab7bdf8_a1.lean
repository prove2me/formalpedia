-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:24.752849+00:00
-- url     : https://prove2.me/submissions/3a55467f-a0d8-47fe-b705-3e0659a4281e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, H <= J → HasPlanarDrawingOn J → J <= H) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1 H hH hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1 H hH hV hmax
  omega