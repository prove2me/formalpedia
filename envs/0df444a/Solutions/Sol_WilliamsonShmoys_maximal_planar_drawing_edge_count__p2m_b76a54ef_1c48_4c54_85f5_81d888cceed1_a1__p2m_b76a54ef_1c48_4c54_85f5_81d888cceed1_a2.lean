-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a1__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:47:51.275651+00:00
-- url     : https://prove2.me/submissions/2396287e-caa2-4d71-a80d-fd31eec4306a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
      H hV hH
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
      H hV hH hmax
  omega