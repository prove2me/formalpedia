-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:14.603308+00:00
-- url     : https://prove2.me/submissions/bcb6a6af-37c9-4d1c-9f31-8577b42151a8

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
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ C.supp.ncard) :
    M.edgeSet.ncard + 6 ≤ 3 * C.supp.ncard := by
  have hs : C.supp.ncard = Fintype.card C.supp := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc M (by omega) hDraw
  omega
