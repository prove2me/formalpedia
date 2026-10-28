-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_95ea5390
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:12:40.573158+00:00
-- url     : https://prove2.me/submissions/0eeeb831-66db-41cb-ad79-0cc98b101c27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_euler_edge_count_95ea5390

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_completion_with_exact_euler_edge_count_95ea5390 M hM hV
  have hEq : N = M := hmax N hMN hN
  subst N
  exact hcount