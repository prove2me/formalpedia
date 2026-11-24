-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_augmentation_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:21.06014+00:00
-- url     : https://prove2.me/submissions/8061427c-3f1a-4f42-80f1-525263b36991

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
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K ∧
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc L hL
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hCard
  exact ⟨H0, hGH0, hC0, hH0, hle0⟩
