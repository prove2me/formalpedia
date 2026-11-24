-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bounds__p2m_5f4b31de_07d6_4550_bc2e_2bb318dd0027_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:15.364746+00:00
-- url     : https://prove2.me/submissions/d978a06c-efe5-4073-bd55-b9a7dae22244

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
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    Fintype.card V ≤ H.edgeSet.ncard + 2 ∧
      H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hMax' : ∀ J : SimpleGraph _, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hHJ hJ
    have := hmax J (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) hJ
    exact (SimpleGraph.edgeSet_inj.mp this).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hcard hplanar hMax'
  constructor <;> omega
