-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_large__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:07:29.04006+00:00
-- url     : https://prove2.me/submissions/a2125f51-ee36-4bea-8757-a051a501ee35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_extension__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 3 ≤ 3 * Fintype.card V := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨H, dH, hHdraw, hsub, hcard_mono, hmax⟩ :=
    WilliamsonShmoys.connected_planar_maximal_extension__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
      G dG hG hconn hcard
  letI : DecidableRel H.Adj := dH
  have hHbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
      H dH hHdraw hcard hmax
  omega