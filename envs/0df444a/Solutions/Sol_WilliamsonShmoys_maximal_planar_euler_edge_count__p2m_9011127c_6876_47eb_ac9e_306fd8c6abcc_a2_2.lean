-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_euler_edge_count__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:00.276494+00:00
-- url     : https://prove2.me/submissions/731a67eb-4db1-4a64-a162-185846a5277b

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
    N.edgeSet.ncard + 6 = 3 * (Set.univ : Set V).ncard := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at *
  have hMax' : ∀ J : SimpleGraph _, N ≤ J → HasPlanarDrawingOn J → J ≤ N := by
    intro J hHJ hJ
    exact SimpleGraph.edgeSet_subset_edgeSet.mp (hMax J hJ (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ))
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc N hcard hDraw hMax'
  omega
