-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_connected__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:31.266834+00:00
-- url     : https://prove2.me/submissions/fc9b1e87-27dd-468f-819c-fc00d49354dd

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
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    M.Connected := by
  have hMax' : ∀ J : SimpleGraph _, M ≤ J → HasPlanarDrawingOn J → J ≤ M := by
    intro J hHJ hJ
    exact (hMax J hHJ hJ).le
  exact WilliamsonShmoys.maximal_planar_drawingOn_connected M hM hMax' hV
