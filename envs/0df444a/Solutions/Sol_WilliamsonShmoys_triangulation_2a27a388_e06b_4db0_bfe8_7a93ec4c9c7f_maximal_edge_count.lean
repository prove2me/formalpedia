-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:35:34.019979+00:00
-- url     : https://prove2.me/submissions/42aebdba-675f-4f46-9e37-d6ccb816ba74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_planar_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_planar_edge_count_upper_bound
    (V := V) K hV hK
  have hlower := WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count_lower_bound
    (V := V) K hV hK hmax
  omega
