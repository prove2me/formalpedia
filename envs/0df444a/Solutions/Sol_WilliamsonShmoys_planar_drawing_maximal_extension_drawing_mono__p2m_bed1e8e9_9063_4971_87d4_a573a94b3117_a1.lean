-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_drawing_mono__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:04:32.007988+00:00
-- url     : https://prove2.me/submissions/f3f61e8b-3897-47b7-85a9-a74a4b9c0816

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V) (hGK : G ≤ K) (hK : HasPlanarDrawingOn K) :
    HasPlanarDrawingOn G := by
  dsimp [HasPlanarDrawingOn] at hK ⊢
  rcases hK with ⟨p, arc, hp, hdraw, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hdraw u v huv (hGK hadj)
  · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
    exact hcross u v x y huv hxy (hGK hadj₁) (hGK hadj₂) hne t ht s hs heq