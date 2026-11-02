-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:45:32.601546+00:00
-- url     : https://prove2.me/submissions/4d4e4fa9-00fe-4b4c-9b0d-d2baaf293d00

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) (hH : HasPlanarDrawingOn H) :
    HasPlanarDrawingOn G := by
  simp only [HasPlanarDrawingOn] at hH ⊢
  rcases hH with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hEdges u v huv (hGH hadj)
  · intro u v x y huv hxy hadj hxyadj hne t ht s hs hEq
    exact hCrossings u v x y huv hxy (hGH hadj) (hGH hxyadj) hne t ht s hs hEq