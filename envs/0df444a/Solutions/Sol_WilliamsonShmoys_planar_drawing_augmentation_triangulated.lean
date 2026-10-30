-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_triangulated
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:12:17.493566+00:00
-- url     : https://prove2.me/submissions/c0e89696-89d3-4526-ab5e-8c7fb83e9390

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_retry_49abde41
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_retry_49abde41

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_retry_49abde41 G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_retry_49abde41 H hH hmax hCard
  exact ⟨H, hGH, hH, hcount⟩