-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_extension_98d9ecda
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:34:51.729519+00:00
-- url     : https://prove2.me/submissions/37b60810-7d9d-4d5b-bfdd-591190b55e7a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_extension_edge_count_3n_minus_6__p2m_9f8c31a1_ded7_4202_9963_82cfbd43c092_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hDraw : HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X = W) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨X, hWX, hDrawX, hCount⟩ :=
    WilliamsonShmoys.planar_drawingOn_extension_edge_count_3n_minus_6__p2m_9f8c31a1_ded7_4202_9963_82cfbd43c092_a4
      W hDraw hCard
  have hXW : X = W := hMax X hWX hDrawX
  simpa [hXW] using hCount