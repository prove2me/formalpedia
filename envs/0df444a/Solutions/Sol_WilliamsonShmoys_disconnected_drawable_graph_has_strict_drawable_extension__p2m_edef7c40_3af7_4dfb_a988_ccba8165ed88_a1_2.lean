-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_drawable_graph_has_strict_drawable_extension__p2m_edef7c40_3af7_4dfb_a988_ccba8165ed88_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:36.809804+00:00
-- url     : https://prove2.me/submissions/52ee6c5d-2c83-4eaa-bb70-004deb129173

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
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ L.Connected) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧ L ≠ M := by
  obtain ⟨J, h1, h2, h3⟩ := WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing L hL hCard hNotConnected
  exact ⟨J, h3, h1, Ne.symm h2⟩
