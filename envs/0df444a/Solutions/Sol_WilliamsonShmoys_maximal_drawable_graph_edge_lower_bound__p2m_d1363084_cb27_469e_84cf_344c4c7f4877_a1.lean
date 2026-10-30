-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:33:47.277641+00:00
-- url     : https://prove2.me/submissions/83a944b2-106c-4b4c-8b69-8ac2772d8b25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_graph_completion_edge_count__p2m_975201d3_ed40_44be_a94c_66f3df904250_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V,
      K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  classical
  obtain ⟨H, hHdec, hKH, hHdraw, hHcard⟩ :=
    WilliamsonShmoys.planar_drawable_graph_completion_edge_count__p2m_975201d3_ed40_44be_a94c_66f3df904250_a1
      K hK hcard
  letI : DecidableRel H.Adj := hHdec
  have hHK : H ≤ K := hmax H hKH hHdraw
  have hEdges : H.edgeFinset.card ≤ K.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
  exact hHcard.le.trans hEdges