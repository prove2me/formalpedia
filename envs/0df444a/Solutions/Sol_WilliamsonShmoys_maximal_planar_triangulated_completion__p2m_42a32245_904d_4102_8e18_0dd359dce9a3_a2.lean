-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulated_completion__p2m_42a32245_904d_4102_8e18_0dd359dce9a3_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:28.916723+00:00
-- url     : https://prove2.me/submissions/182491cc-4f6f-46db-a00f-683364179e19

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 <= Fintype.card V) (hDraw : HasPlanarDrawingOn L) : Exists fun M : SimpleGraph V => L <= M /\ HasPlanarDrawingOn M /\ 3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨H0, hGH0, hH0, hle, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc L hV hDraw
  exact ⟨H0, hGH0, hH0, by omega⟩
