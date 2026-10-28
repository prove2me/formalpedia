-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:31:12.70599+00:00
-- url     : https://prove2.me/submissions/3c7cc6c6-77cb-46c4-a428-096976c4b163
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion M hV hM
  have hNM : N = M := hmax N hMN hN
  have hEq : 3 * Fintype.card V - 6 = M.edgeSet.ncard := by
    simpa [hNM] using hcount.symm
  exact hEq.le