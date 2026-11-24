-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:01.152719+00:00
-- url     : https://prove2.me/submissions/41deb434-4fc9-42b3-9522-8323399931ac

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
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ (Set.univ : Set V).ncard)
    (hMax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet → P.edgeSet ⊆ N.edgeSet) :
    3 * (Set.univ : Set V).ncard ≤ N.edgeSet.ncard + 6 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at *
  have hMax' : ∀ J : SimpleGraph _, N ≤ J → HasPlanarDrawingOn J → J ≤ N := by
    intro J hHJ hJ
    exact SimpleGraph.edgeSet_subset_edgeSet.mp (hMax J hJ (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ))
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc N hcard hDraw hMax'
  omega
