-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_is_connected__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:52.92479+00:00
-- url     : https://prove2.me/submissions/ebf3995a-820b-401e-867b-039a0cff98a1

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P) (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) : P.Connected := by
  exact WilliamsonShmoys.maximal_planar_drawingOn_connected P hP hMax hV
