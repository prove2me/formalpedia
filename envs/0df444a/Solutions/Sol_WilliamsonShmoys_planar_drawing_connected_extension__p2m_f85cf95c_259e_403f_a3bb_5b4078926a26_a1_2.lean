-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:03.303439+00:00
-- url     : https://prove2.me/submissions/33dc81de-37fe-46d1-909e-b2857846df05

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
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hT : HasPlanarDrawingOn T) :
    ∃ H : SimpleGraph V, T.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc T hT
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
  exact ⟨H0, SimpleGraph.edgeSet_subset_edgeSet.mpr hGH0, hC0, hH0⟩
