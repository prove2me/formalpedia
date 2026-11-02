-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:04:16.930764+00:00
-- url     : https://prove2.me/submissions/8cdf2caa-f496-4599-aa07-98e453efffc9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, h_edges, h_crossings⟩
  have h_sub : ∀ {u v : V}, G.Adj u v → H.Adj u v := by
    intro u v huv
    change s(u, v) ∈ G.edgeSet at huv
    have hmem : s(u, v) ∈ H.edgeSet := hGH huv
    change H.Adj u v
    exact hmem
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact h_edges u v huv (h_sub hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs hEq
    exact h_crossings u v x y huv hxy
      (h_sub hGuv) (h_sub hGxy) hne t ht s hs hEq