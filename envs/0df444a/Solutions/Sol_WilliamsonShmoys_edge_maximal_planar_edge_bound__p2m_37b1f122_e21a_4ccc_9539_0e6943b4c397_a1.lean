-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:58.744885+00:00
-- url     : https://prove2.me/submissions/dd421b4c-6acc-4c11-8d33-3fa809e89201
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawing_face_count__p2m_8d49dd8d_df70_44ed_9374_0df305c3481e_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    3 * Fintype.card V ≤ T.edgeFinset.card + 6 := by
  classical
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.edge_maximal_drawing_face_count__p2m_8d49dd8d_df70_44ed_9374_0df305c3481e_a2
      T hT hmax hcard
  omega