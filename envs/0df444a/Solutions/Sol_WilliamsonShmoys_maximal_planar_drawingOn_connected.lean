-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:42:05.559678+00:00
-- url     : https://prove2.me/submissions/a88c534c-36d3-450e-aa50-9bdc8f50f732
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_add_edge_across_components

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J)
    (hCard : 3 ≤ Fintype.card V) :
    J.Connected := by
  by_contra hNotConnected
  obtain ⟨u, v, huv, hNotAdj, K, hJK, hKuv, hKDraw⟩ :=
    WilliamsonShmoys.planarDrawingOn_add_edge_across_components J hDraw hNotConnected
  have hKJ : K ≤ J := hMax K hJK hKDraw
  exact hNotAdj (hKJ hKuv)