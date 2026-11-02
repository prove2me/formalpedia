-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:57:40.014653+00:00
-- url     : https://prove2.me/submissions/20de8ddd-f9f9-4826-95c6-723143e6fca7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     3 * Fintype.card V - 6 = K.edgeFinset.card) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hupper := WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1 K hV hK
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1 K hV hK hmax
  omega