-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:39:07.91153+00:00
-- url     : https://prove2.me/submissions/b255abb0-afb8-4953-97ae-043078147383

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : Set.Subset G.edgeSet H.edgeSet) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  have hle : ∀ u v, G.Adj u v → H.Adj u v := fun u v h => by
    have : s(u, v) ∈ H.edgeSet := hGH (by simpa using h)
    simpa using this
  exact ⟨p, arc, hp, fun u v huv hG => h1 u v huv (hle u v hG),
    fun u v x y huv hxy hG hG' hne => h2 u v x y huv hxy (hle u v hG) (hle x y hG') hne⟩
