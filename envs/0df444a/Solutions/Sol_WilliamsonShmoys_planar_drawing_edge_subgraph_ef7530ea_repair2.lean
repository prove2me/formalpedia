-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_subgraph_ef7530ea_repair2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:14:02.830669+00:00
-- url     : https://prove2.me/submissions/252993eb-fe5e-4a9f-8a17-0f547e5045e1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : ∀ u v, G.Adj u v → H.Adj u v)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv hadj => h1 u v huv (hGH u v hadj),
    fun u v x y huv hxy ha hb hne => h2 u v x y huv hxy (hGH u v ha) (hGH x y hb) hne⟩
