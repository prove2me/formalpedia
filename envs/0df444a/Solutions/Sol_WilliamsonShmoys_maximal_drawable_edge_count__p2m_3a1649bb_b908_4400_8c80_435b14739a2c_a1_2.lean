-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:25.423004+00:00
-- url     : https://prove2.me/submissions/27d35bb9-210f-40b0-986a-7c0edd0c422d

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
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ L : SimpleGraph V,
      M.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      M.edgeSet = L.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hMax' : ∀ J : SimpleGraph _, M ≤ J → HasPlanarDrawingOn J → J ≤ M := by
    intro J hHJ hJ
    exact (SimpleGraph.edgeSet_inj.mp (hMax J (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) hJ)).ge
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc M hCard hM hMax'
  omega
