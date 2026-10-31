-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:13:07.055357+00:00
-- url     : https://prove2.me/submissions/4543e5ee-d508-4076-82ec-6f4f33fa0e19

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hle, hH, hconn⟩ :=
    WilliamsonShmoys.planar_connected_extension__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
      K hK hV
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
      H hH hconn hV
  omega