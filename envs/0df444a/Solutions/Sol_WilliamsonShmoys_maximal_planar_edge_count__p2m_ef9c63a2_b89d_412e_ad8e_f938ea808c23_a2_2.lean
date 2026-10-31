-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:30:50.217634+00:00
-- url     : https://prove2.me/submissions/6d33ad58-4c66-4a4b-8308-f0f7ba9195a1

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd K hK hV hmax
