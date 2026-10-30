-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_mono__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:36.550691+00:00
-- url     : https://prove2.me/submissions/156f9b1e-9417-48b4-af7d-d035b69a41a0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] {H K : SimpleGraph V}
    (hHK : H ≤ K) (hK : HasPlanarDrawingOn K) : HasPlanarDrawingOn H := by
  rcases hK with ⟨p, arc, hp, hEdges, hNoCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hAdj
    exact hEdges u v huv (hHK hAdj)
  · intro u v x y huv hxy hAdjUV hAdjXY hDifferent t ht s hs hArcEq
    exact hNoCrossings u v x y huv hxy (hHK hAdjUV) (hHK hAdjXY)
      hDifferent t ht s hs hArcEq