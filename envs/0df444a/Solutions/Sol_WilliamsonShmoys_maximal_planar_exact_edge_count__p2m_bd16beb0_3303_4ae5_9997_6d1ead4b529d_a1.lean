-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:54.784559+00:00
-- url     : https://prove2.me/submissions/02c9261b-540b-4077-a8e4-1238e91fed29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_4344ea89_6f5a_4717_bdab_0b5d693cf9ed_a3
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      (∀ u v, M.Adj u v → N.Adj u v) → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hN, hsub, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_4344ea89_6f5a_4717_bdab_0b5d693cf9ed_a3
      M hM hcard
  have hNM : N = M := hmax N hN hsub
  simpa only [hNM] using hcount