-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_extension__p2m_3e4841aa_5cc8_43c5_ada3_9b4132733a6e_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:31.919537+00:00
-- url     : https://prove2.me/submissions/160a9949-515c-4bba-9fea-98d1fdec5fbf

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
    (hconn : ¬ L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ ¬ H ≤ L := by
  obtain ⟨J, h1, h2, h3⟩ := WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing L hL hV hconn
  exact ⟨J, h1, h3, fun h => h2 (le_antisymm h h1)⟩
