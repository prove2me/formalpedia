-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:46:27.861403+00:00
-- url     : https://prove2.me/submissions/3d875607-80ec-4d91-a022-6fec0d69ea94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion__p2m_ae2deb14_265a_4589_b20a_d2c312b9c2e6_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : ∀ H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
  obtain ⟨H, hGH, _hHdrawing, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_completion__p2m_ae2deb14_265a_4589_b20a_d2c312b9c2e6_a1
      G hcard hdrawing
  exact (Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)).trans (le_of_eq hHcard)