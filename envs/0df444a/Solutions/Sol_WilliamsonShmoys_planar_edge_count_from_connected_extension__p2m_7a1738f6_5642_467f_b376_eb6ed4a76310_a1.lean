-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_from_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:13.910055+00:00
-- url     : https://prove2.me/submissions/c3c34412-93e0-4b7f-b918-5fb9947a4948

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_d40c3a6b_3de6_46aa_9fd1_14fe5823e11e_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hKH : K ≤ H)
    (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have hsub : K.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hKH
  exact (Set.ncard_mono hsub).trans
    (WilliamsonShmoys.connected_planar_edge_count_bound__p2m_d40c3a6b_3de6_46aa_9fd1_14fe5823e11e_a1
      H hV hHconn hHplanar)