-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_8e6fe4ee_76fd_4caa_8f38_7058c432af92
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:56.396279+00:00
-- url     : https://prove2.me/submissions/5f21505c-f05a-47d5-9bb9-f2365d17ca26

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K H : SimpleGraph V) (hKH : K ≤ H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  refine ⟨Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hKH) (Set.toFinite _), ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hCard hH hMax
