-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_edge_count_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:21:57.988181+00:00
-- url     : https://prove2.me/submissions/6a255547-c02a-49ff-994d-a9969804bc47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_edge_count_91679e32
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_completion_91679e32

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hNplanar, hNmaximal⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_for_edge_count_91679e32
      M hMplanar
  have hCount :=
    WilliamsonShmoys.maximal_drawable_edge_count_for_completion_91679e32
      N hNplanar hV hNmaximal
  exact ⟨N, hMN, hNplanar, hCount⟩