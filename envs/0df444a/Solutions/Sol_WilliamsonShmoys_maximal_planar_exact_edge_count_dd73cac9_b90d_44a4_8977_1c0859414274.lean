-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:31:00.778829+00:00
-- url     : https://prove2.me/submissions/bf47725c-c43e-4fde-96fc-70e046bfac7b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_planar_exact_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_exact_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_upper_bound_for_maximal_planar_exact_edge_count K hK hCard
  · exact WilliamsonShmoys.maximal_planar_edge_lower_bound_for_exact_edge_count K hK hCard hMax
