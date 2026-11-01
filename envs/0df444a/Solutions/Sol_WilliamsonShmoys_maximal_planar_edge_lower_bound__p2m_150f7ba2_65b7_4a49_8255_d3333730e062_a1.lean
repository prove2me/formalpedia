-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:03.183941+00:00
-- url     : https://prove2.me/submissions/f3ff2d42-3303-43fa-99f0-95d459950d74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_7ffdcecf_da07_45cb_a4da_fb98455db8ef_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ L : SimpleGraph V,
      (∀ u v, G.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨L, hsub, hL, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_7ffdcecf_da07_45cb_a4da_fb98455db8ef_a1
      G hcard hG
  have hLG : L = G := hmax L hsub hL
  simpa [hLG] using hcount.le