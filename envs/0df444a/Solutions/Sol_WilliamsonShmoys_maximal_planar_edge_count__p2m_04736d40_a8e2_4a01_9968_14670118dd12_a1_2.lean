-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:49:44.24377+00:00
-- url     : https://prove2.me/submissions/f98fea0f-6a4c-4fb8-b72a-8818770aa019

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd K hK hV hmax
