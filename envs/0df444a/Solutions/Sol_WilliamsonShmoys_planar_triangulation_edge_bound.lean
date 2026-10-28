-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:32:33.826069+00:00
-- url     : https://prove2.me/submissions/3b1a794a-1bf6-4084-beec-12efc2f2d7be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hGK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph G hG
  exact ⟨K, hGK, hKplanar,
    WilliamsonShmoys.maximal_planar_graph_edge_bound K hKplanar hV hKmax⟩