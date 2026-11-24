-- Prove2me | solution 3 for WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:30.543824+00:00
-- url     : https://prove2.me/submissions/ad6db92e-d368-4952-84ec-e74c3ad2e605

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) : H.Connected := by
  have hMax' : ∀ J : SimpleGraph _, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hHJ hJ
    exact (hmax J hHJ hJ).le
  exact WilliamsonShmoys.maximal_planar_drawingOn_connected H hH hMax' hcard
