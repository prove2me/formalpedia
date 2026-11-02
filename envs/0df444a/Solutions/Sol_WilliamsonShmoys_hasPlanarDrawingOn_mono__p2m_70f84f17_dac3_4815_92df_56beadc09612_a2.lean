-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:07:13.546682+00:00
-- url     : https://prove2.me/submissions/50da0bba-4965-4bcc-96a3-331ab223664f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hHG hadj)
  · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
    exact hcross u v x y huv hxy (hHG hadj₁) (hHG hadj₂) hne t ht s hs heq