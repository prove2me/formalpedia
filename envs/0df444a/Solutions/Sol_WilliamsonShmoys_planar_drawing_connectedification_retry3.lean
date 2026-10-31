-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connectedification_retry3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:25:55.04265+00:00
-- url     : https://prove2.me/submissions/0e36b316-e844-4701-9fde-c6451d710290

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_connectedification_retry3
import Theorems.Thm_WilliamsonShmoys_disconnected_drawing_proper_extension_connectedification_retry3
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hSub, hEdges, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_connectedification_retry3 G hDraw
  have hConnected : H.Connected := by
    by_contra hNotConnected
    obtain ⟨K, hHK, hNe, hDrawK⟩ :=
      WilliamsonShmoys.disconnected_drawing_proper_extension_connectedification_retry3
        H hDrawH hCard hNotConnected
    exact hNe (hMax K hHK hDrawK)
  exact ⟨H, hEdges, hConnected, hDrawH⟩