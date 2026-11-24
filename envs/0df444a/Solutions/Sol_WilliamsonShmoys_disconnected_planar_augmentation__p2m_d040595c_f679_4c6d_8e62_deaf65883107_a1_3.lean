-- Prove2me | solution 3 for WilliamsonShmoys.disconnected_planar_augmentation__p2m_d040595c_f679_4c6d_8e62_deaf65883107_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:35.322552+00:00
-- url     : https://prove2.me/submissions/026cb080-a972-42cb-b40b-7adb1e02fbc3

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
    (hDisc : ¬ M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N ≠ M ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by
  exact WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing M hM hV hDisc
