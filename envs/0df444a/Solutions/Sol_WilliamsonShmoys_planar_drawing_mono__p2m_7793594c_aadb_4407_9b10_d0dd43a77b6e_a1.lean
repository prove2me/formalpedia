-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_mono__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:20.496235+00:00
-- url     : https://prove2.me/submissions/faa3e45f-4435-43bd-8e99-282d3892e4ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] {G K : SimpleGraph V}
    (hGK : G ≤ K) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hK with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hEdges u v huv (hGK hG)
  · intro u v x y huv hxy hG hG' hne
    exact hCrossings u v x y huv hxy (hGK hG) (hGK hG') hne