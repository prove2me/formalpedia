-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:47:51.701286+00:00
-- url     : https://prove2.me/submissions/ced75dc8-46fc-45f3-aa70-71bed503ebdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_counts__p2m_3e25b6a0_4b21_4d35_9051_eedb215386d1_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by
  obtain ⟨f, hIncidence, hEuler⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_has_triangulation_counts__p2m_3e25b6a0_4b21_4d35_9051_eedb215386d1_a2
      H hH hmax hV
  omega