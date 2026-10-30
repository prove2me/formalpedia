-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:47:47.475077+00:00
-- url     : https://prove2.me/submissions/6248e572-72ce-4e9d-b5f5-9236001c8151

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists_maximal_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V, H <= K /\ HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_maximal_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd H hH
  have hEdges :=
    WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd K hK hCard hMax
  exact ⟨K, hHK, hK, hEdges⟩