-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_face_counts__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:13:57.759993+00:00
-- url     : https://prove2.me/submissions/3afac769-cdf3-4a76-9d01-68dcdcf1d2ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1

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
    exists f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 /\
      3 * f = 2 * H.edgeSet.ncard := by
  have hup :
      H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
      H hH hV
  have hlo :
      3 * Fintype.card V <= H.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
      H hH hmax hV
  have hedge : 6 + H.edgeSet.ncard = 3 * Fintype.card V := by omega
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega
