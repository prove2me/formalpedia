-- Prove2me | solution 1 for WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_edge_count__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:25:00.823503+00:00
-- url     : https://prove2.me/submissions/a503c3b4-f58a-4df6-8965-34a5d0ec6568
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_planar_edge_count_upper__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hQ : HasPlanarDrawingOn Q)
    (hmax : forall R : SimpleGraph V, Q <= R -> HasPlanarDrawingOn R -> R <= Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    Q.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
  have hu := WilliamsonShmoys.WilliamsonShmoys_planar_edge_count_upper__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5 Q hV hQ
  have hl := WilliamsonShmoys.WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5 Q hV hQ hmax
  omega