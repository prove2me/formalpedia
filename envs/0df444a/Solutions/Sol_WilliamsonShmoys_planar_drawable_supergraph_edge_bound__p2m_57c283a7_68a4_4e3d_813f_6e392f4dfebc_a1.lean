-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_supergraph_edge_bound__p2m_57c283a7_68a4_4e3d_813f_6e392f4dfebc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:29:02.470926+00:00
-- url     : https://prove2.me/submissions/dd1e78d5-acc9-4fb6-ab43-e422766ad749
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_extension__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawable_edge_bound__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, HasPlanarDrawingOn N ∧ M ≤ N ∧
      ∀ [DecidableRel N.Adj], 3 * Fintype.card V - 6 ≤ N.edgeFinset.card := by
  obtain ⟨N, hN, hMN, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_supergraph_extension__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
      M hM hcard
  refine ⟨N, hN, hMN, ?_⟩
  intro _
  exact WilliamsonShmoys.maximal_planar_drawable_edge_bound__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
    N hN hcard hmax