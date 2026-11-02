-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:54:38.991748+00:00
-- url     : https://prove2.me/submissions/e73ee456-9954-4af2-8cba-df3c70c222e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
    H hH hCard
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
    H hH hMaximal hCard
  omega