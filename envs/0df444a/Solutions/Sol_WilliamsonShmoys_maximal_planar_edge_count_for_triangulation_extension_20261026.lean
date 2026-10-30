-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:59:45.858775+00:00
-- url     : https://prove2.me/submissions/e5f27a84-a9d9-468d-a43b-91edb5a30ddb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension_20261026_planar_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension_20261026_maximal_planar_edge_count_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026_planar_edge_count_upper_bound
    H hH hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026_maximal_planar_edge_count_lower_bound
    H hH hmax hV
  omega