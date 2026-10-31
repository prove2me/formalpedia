-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:28:29.47998+00:00
-- url     : https://prove2.me/submissions/d7f7407f-9731-4950-9274-05f4dd8aa6f9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hMax : forall J : SimpleGraph V, H <= J -> HasPlanarDrawingOn J -> J = H)
    (hConn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
      H hPlanar hConn hV
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
      H hPlanar hMax hConn hV
  omega