-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:41:32.554783+00:00
-- url     : https://prove2.me/submissions/32863c15-0ad2-451a-95bb-c1e1a41a2704
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, _hDrawH, htri⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
      G hDraw hV
  exact le_trans
    (WilliamsonShmoys.edgeSet_ncard_mono__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
      G H hsub)
    htri.le