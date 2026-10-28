-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:38:34.8596+00:00
-- url     : https://prove2.me/submissions/48d43b20-b65a-4b2b-abca-7efdff2ae010
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count_b2facf4f_375b_4f83_ba19_34094f723a5d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V,
      M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_maximal_edge_count_b2facf4f_375b_4f83_ba19_34094f723a5d
      M hV hM
  have hNM : N <= M := hMax N hMN hN
  have hEq : M = N := le_antisymm hMN hNM
  simpa [hEq] using hCount