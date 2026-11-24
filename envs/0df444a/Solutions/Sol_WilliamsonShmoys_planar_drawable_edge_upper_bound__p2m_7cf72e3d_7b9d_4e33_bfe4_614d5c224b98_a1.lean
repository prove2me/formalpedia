-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_upper_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:07.989001+00:00
-- url     : https://prove2.me/submissions/a65b5746-2ead-4a78-8b83-a0d944e0df0c

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) : M.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc M hcard hM
  have e : M.edgeSet.ncard = M.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
