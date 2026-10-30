-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:33:52.243904+00:00
-- url     : https://prove2.me/submissions/51ae7b06-b459-46db-95ed-60787f342717

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_edge_bound_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_lower_bound_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup :=
    WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2 K hV hK hconn
  have hlo :=
    WilliamsonShmoys.maximal_planar_drawing_triangulation_lower_bound_v2
      K hV hK hconn hmax
  omega