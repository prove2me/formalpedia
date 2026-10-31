-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:50.487118+00:00
-- url     : https://prove2.me/submissions/2c70dcfe-bb9e-4c1a-944c-74674ddaebf5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  have hadj_mono : ∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v := by
    intro u v huv
    have hmem : s(u, v) ∈ H.edgeSet := by
      simpa using huv
    have hmemG : s(u, v) ∈ G.edgeSet := hHG hmem
    simpa using hmemG
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hadj_mono hadj)
  · intro u v x y huv hxy hadj huvxy hneq t ht s hs heq
    exact hcross u v x y huv hxy (hadj_mono hadj) (hadj_mono huvxy)
      hneq t ht s hs heq