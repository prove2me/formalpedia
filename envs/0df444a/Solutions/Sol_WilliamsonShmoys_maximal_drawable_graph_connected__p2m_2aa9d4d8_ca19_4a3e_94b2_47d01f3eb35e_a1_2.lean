-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_connected__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:32.108433+00:00
-- url     : https://prove2.me/submissions/d0f2bda7-f818-45b4-8f6e-e35def2c729c

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
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    L.Connected := by
  have hMax' : ∀ J : SimpleGraph _, L ≤ J → HasPlanarDrawingOn J → J ≤ L := by
    intro J hHJ hJ
    exact (hMax J hJ hHJ).ge
  exact WilliamsonShmoys.maximal_planar_drawingOn_connected L hL hMax' hCard
