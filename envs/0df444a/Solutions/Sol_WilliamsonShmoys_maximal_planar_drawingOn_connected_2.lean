-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawingOn_connected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:25:58.475646+00:00
-- url     : https://prove2.me/submissions/6ccfca9d-cc16-4015-ae83-d41e994956ec

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2

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
    WilliamsonShmoys.planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2
      J hDraw hNotConnected hCard
  have hKJ : K ≤ J := hMax K hJK hKDraw
  exact hNotAdj (hKJ hKuv)