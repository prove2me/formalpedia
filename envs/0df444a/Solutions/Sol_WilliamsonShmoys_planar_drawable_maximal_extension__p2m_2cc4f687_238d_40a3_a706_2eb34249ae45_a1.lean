-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_extension__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:22.606909+00:00
-- url     : https://prove2.me/submissions/9a290f96-1a7e-43e0-8cd8-743333e4ed3b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
      G.edgeSet.ncard <= H.edgeSet.ncard /\
      (forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) := by
  exact WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc G hG
