-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_c10b408b_b7ec_40f0_b964_0a6697295590
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:51:47.137216+00:00
-- url     : https://prove2.me/submissions/31052b7d-546b-4f98-8503-dfcaa1ac4f3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_23341804_e9bd_4849_9be7_9e709bd142a9
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_23341804_e9bd_4849_9be7_9e709bd142a9

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_23341804_e9bd_4849_9be7_9e709bd142a9 K hK hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_23341804_e9bd_4849_9be7_9e709bd142a9 K hK hCard hMax
  omega