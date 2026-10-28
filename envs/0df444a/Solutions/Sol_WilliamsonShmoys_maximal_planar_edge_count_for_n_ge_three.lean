-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_n_ge_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:59:41.531327+00:00
-- url     : https://prove2.me/submissions/e0a2b139-9b37-434a-aad1-90f873884342
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.maximal_planar_edge_count_upper_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99 L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99 L hL hMax hCard
  omega