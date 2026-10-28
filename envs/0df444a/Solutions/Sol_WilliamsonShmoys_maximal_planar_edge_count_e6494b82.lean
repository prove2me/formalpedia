-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_e6494b82
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:29:43.683996+00:00
-- url     : https://prove2.me/submissions/24e6be97-71e5-4175-81e2-8f5ff15a04bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulated_extension_e6494b82

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_triangulated_extension_e6494b82
      M hM hCard
  have hEq : N = M := hMax N hMN hN
  simpa [hEq] using hCount