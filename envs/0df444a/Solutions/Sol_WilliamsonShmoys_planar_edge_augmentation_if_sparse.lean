-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_if_sparse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:51:56.957984+00:00
-- url     : https://prove2.me/submissions/72080d2c-fd14-40dc-b896-1de6796a8e3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_fd0d87e6_b805_416b_90da_57eb1ca5807e
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_edge_bound_fd0d87e6_b805_416b_90da_57eb1ca5807e
import Theorems.Thm_WilliamsonShmoys_edge_ncard_mono_fd0d87e6_b805_416b_90da_57eb1ca5807e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ¬ M ≤ L := by
  obtain ⟨M, hLM, hdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_fd0d87e6_b805_416b_90da_57eb1ca5807e L hL
  have hbound :=
    WilliamsonShmoys.maximal_drawable_planar_edge_bound_fd0d87e6_b805_416b_90da_57eb1ca5807e M hV hdraw hmax
  refine ⟨M, hLM, hdraw, ?_⟩
  intro hML
  have hcount :=
    WilliamsonShmoys.edge_ncard_mono_fd0d87e6_b805_416b_90da_57eb1ca5807e M L hML
  omega
