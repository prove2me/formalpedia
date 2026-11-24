-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:25.969798+00:00
-- url     : https://prove2.me/submissions/186a8636-613a-4210-a0ad-ecd1344b0a7e

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
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H) :
    H.edgeSet.ncard = 3 * (Fintype.card V - 2) := by
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hV hH hmax
  omega
