-- Prove2me | solution 1 for WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:30:48.273477+00:00
-- url     : https://prove2.me/submissions/a45ba01a-6c90-417e-9a46-49c766685452
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_count_of_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hNcard⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_count_of_drawing M hV hM
  have hEq : N = M := hmax N hMN hN
  rw [hEq] at hNcard
  omega