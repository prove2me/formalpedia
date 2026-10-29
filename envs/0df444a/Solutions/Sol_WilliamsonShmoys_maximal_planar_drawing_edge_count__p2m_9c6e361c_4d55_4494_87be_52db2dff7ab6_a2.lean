-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:37:31.912927+00:00
-- url     : https://prove2.me/submissions/e123b510-5635-448d-a3e1-c4052e5d5263
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      (forall {u v}, K.Adj u v -> L.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1 K hV hK
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1 K hV hK hmax
  omega