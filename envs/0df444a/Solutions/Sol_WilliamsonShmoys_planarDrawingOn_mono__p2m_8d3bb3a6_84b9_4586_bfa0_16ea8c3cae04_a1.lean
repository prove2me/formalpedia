-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_mono__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:44:53.260118+00:00
-- url     : https://prove2.me/submissions/a8a0a1ff-2211-4ffe-b834-961b1fa65393

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, h_edges, h_pairwise⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact h_edges u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs h_eq
    exact h_pairwise u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs h_eq