-- Prove2me | solution 1 for WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:07:12.933992+00:00
-- url     : https://prove2.me/submissions/1ae4f6b3-0c2d-46ae-be6d-89e56e7f9482

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_maximal_edge_count_20261028_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_maximal_edge_count_20261028_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028_upper_bound K hV hDraw
  · exact WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028_lower_bound K hV hDraw hmax