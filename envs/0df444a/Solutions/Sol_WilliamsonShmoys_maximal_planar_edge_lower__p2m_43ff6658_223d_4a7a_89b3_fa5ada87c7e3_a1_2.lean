-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:44.115315+00:00
-- url     : https://prove2.me/submissions/6167e403-9c7e-474f-8dd9-4271f1fb9256

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
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by
  have hMax' : ∀ J : SimpleGraph _, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hHJ hJ
    exact @hmax J (Classical.decRel _) hJ hHJ
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hcard hH hMax'
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  omega
