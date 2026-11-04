-- Prove2me | solution 1 for WilliamsonShmoys.WilliamsonShmoys_planar_edge_count_upper__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:36:34.853447+00:00
-- url     : https://prove2.me/submissions/b3535148-c480-4902-be16-8168352c9e00

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edgeCount_upper__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have h := WilliamsonShmoys.planar_edgeCount_upper__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1 G hG hV
  omega
