-- Prove2me | solution 3 for WilliamsonShmoys.planar_drawing_disconnected_edge_extension__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:36.084815+00:00
-- url     : https://prove2.me/submissions/6bf5321f-78cd-4c77-87ac-24d25df853ba

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
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K' ≠ K := by
  obtain ⟨J, h1, h2, h3⟩ := WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing K hK hV hDisconnected
  exact ⟨J, h1, h3, h2⟩
