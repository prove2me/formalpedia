-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_upper__p2m_341f0f70_acb5_465d_8404_ec7db43234c5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:46:43.954277+00:00
-- url     : https://prove2.me/submissions/79cc2ed5-c479-41e5-838c-67ce22090621

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_upper_b94a5187

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_drawable_supergraph_edge_count_upper_b94a5187 K hCard hK