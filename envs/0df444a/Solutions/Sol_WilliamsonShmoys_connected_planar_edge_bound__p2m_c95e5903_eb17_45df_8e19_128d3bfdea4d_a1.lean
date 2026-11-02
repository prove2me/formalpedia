-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:54:33.531137+00:00
-- url     : https://prove2.me/submissions/083818be-b2a1-4c81-aaee-716a9402e7a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
import Theorems.Thm_WilliamsonShmoys_euler_face_data_edge_bound__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases WilliamsonShmoys.drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
      G hG hconn hcard with ⟨faceCount, boundaryLength, hEuler, hIncidence, hLength⟩
  exact WilliamsonShmoys.euler_face_data_edge_bound__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
    G faceCount boundaryLength hEuler hIncidence hLength hcard