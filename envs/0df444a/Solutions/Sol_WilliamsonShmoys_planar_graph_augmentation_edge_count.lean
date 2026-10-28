-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augmentation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:42:09.477596+00:00
-- url     : https://prove2.me/submissions/2f126fbd-dd41-4ad6-9771-8da3c94c0e66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_exists_a0798f51_6e18_4401_9598_620a32b64bfd
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_a0798f51_6e18_4401_9598_620a32b64bfd

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hMplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_supergraph_exists_a0798f51_6e18_4401_9598_620a32b64bfd
      L hLplanar
  refine ⟨M, hLM, hMplanar, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count_a0798f51_6e18_4401_9598_620a32b64bfd
    M hV hMplanar hmax