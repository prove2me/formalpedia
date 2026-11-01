-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:08.447288+00:00
-- url     : https://prove2.me/submissions/8340567d-018f-44ce-a9b0-1ee079b49bdd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hsub : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  have hle : H ≤ G := SimpleGraph.edgeSet_subset_edgeSet.mp hsub
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hH
    exact hedge u v huv (hle hH)
  · intro u v x y huv hxy hHuv hHxy hne t ht s hs hEq
    exact hcross u v x y huv hxy (hle hHuv) (hle hHxy) hne t ht s hs hEq