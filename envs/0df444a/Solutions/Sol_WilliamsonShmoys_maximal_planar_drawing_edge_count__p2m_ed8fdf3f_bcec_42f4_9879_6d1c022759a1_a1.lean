-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:19:39.157227+00:00
-- url     : https://prove2.me/submissions/8cd271e9-0fba-4883-9032-7c5eba726a68

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd K hK hCard hMax
