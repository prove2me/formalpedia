-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_1b39b828_58fc_4ef1_a477_eeaba85e9424
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:19:50.983964+00:00
-- url     : https://prove2.me/submissions/f73fc4b0-583f-40e4-95e1-eff93947e15c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_4a969e66

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNplanar, hNcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph_4a969e66 M hM hCard
  have hNM : N = M := hmax N hMN hNplanar
  simpa [hNM] using hNcard