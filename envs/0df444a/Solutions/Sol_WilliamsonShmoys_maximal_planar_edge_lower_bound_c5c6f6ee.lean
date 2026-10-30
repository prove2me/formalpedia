-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:06:01.426615+00:00
-- url     : https://prove2.me/submissions/0a95a6b5-eb1d-4fb9-a396-45f55e77fa04

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_with_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_with_euler_edge_count M hV hM
  have hNM : N = M := hmax N hMN hN
  simpa only [hNM] using hcount.le