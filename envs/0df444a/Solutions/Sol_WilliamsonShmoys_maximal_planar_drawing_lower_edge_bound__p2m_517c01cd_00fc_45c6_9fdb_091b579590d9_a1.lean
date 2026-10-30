-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_lower_edge_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:08.883945+00:00
-- url     : https://prove2.me/submissions/bfea3ff9-4368-4fda-b000-1a52dbacb28e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_euler_face_counts__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
import Theorems.Thm_WilliamsonShmoys_euler_face_counts_imply_planar_edge_bound__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.maximal_drawing_has_euler_face_counts__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
      K hK hV hmax
  exact WilliamsonShmoys.euler_face_counts_imply_planar_edge_bound__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
    K f heuler hfaces