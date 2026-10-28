-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:59:24.955323+00:00
-- url     : https://prove2.me/submissions/9b03f2e6-03cb-4c4c-80ad-f248a89f9cdc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, h_edges, h_crossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact h_edges u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact h_crossings u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs heq