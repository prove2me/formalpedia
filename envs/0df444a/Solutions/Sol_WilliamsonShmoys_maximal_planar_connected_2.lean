-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_connected
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:29.421461+00:00
-- url     : https://prove2.me/submissions/cbd50685-2f64-4b7a-86a2-2014fdb03c8c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.Connected := by
  have hMax' : ∀ J : SimpleGraph _, L ≤ J → HasPlanarDrawingOn J → J ≤ L := by
    intro J hHJ hJ
    exact (hMax J hHJ hJ).le
  exact WilliamsonShmoys.maximal_planar_drawingOn_connected L hL hMax' hCard
