-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_for_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:00:40.025028+00:00
-- url     : https://prove2.me/submissions/dd2ec3d7-c4b2-40b7-bf9e-2c45954722a6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound_af1db6be
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_af1db6be

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :
      K.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_graph_edge_count_upper_bound_af1db6be K hV hK
  have hlower :
      3 * Fintype.card V - 6 <= K.edgeSet.ncard :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_af1db6be K hV hK hmax
  omega