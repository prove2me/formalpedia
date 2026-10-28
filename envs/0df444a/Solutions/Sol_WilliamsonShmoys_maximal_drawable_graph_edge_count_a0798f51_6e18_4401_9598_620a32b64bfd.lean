-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_a0798f51_6e18_4401_9598_620a32b64bfd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:59:12.634606+00:00
-- url     : https://prove2.me/submissions/1b1200e4-cb74-4b8c-8a3c-4e631fb57d13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_count_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hNplanar, hNcount⟩ :=
    WilliamsonShmoys.exists_drawable_edge_count_completion M hMplanar hV
  have hNM : N = M := hmax N hMN hNplanar
  simpa [hNM] using hNcount