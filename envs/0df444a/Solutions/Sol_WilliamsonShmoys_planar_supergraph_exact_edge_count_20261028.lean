-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exact_edge_count_20261028
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:18:59.392709+00:00
-- url     : https://prove2.me/submissions/39d877f8-7b72-47b2-9cd5-5807c6486eac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_maximal_supergraph_20261028
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_20261028

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_planar_maximal_supergraph_20261028 G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.planar_maximal_edge_count_20261028 H hH hMax hCard⟩