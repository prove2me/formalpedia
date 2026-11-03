-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:53:38.668489+00:00
-- url     : https://prove2.me/submissions/aeddde1a-056a-478b-ad0e-2fab57872451

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_30cffe24_7203_4ddb_9bd1_f31532d2c872_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  rcases WilliamsonShmoys.planar_drawing_face_data__p2m_30cffe24_7203_4ddb_9bd1_f31532d2c872_a2
      K dK hconn hK hcard with
    ⟨f, l, hEuler, hBoundary, hIncidence⟩
  omega