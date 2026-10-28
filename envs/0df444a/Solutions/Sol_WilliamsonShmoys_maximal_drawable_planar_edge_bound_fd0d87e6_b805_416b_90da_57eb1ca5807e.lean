-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_planar_edge_bound_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:10:49.640048+00:00
-- url     : https://prove2.me/submissions/3cad7fc3-8cc8-4f8f-aeae-fab2d4513ee7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_edge_count_extension M hV hM
  have hNM : N ≤ M := hmax N hMN hN
  have hEq : M = N := le_antisymm hMN hNM
  rw [hEq]
  exact le_of_eq hcount