-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_merge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:55:40.489368+00:00
-- url     : https://prove2.me/submissions/3008ebec-c9ae-4c4b-8a83-03ea71a53779
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_component_link_exists
import Theorems.Thm_WilliamsonShmoys_component_count_decreases_after_link

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hDisconnected : ¬ Y.Connected)
    (iY : Fintype Y.ConnectedComponent) :
    ∃ (Z : SimpleGraph V), ∃ (iZ : Fintype Z.ConnectedComponent),
      Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
        @Fintype.card Z.ConnectedComponent iZ <
          @Fintype.card Y.ConnectedComponent iY := by
  obtain ⟨Z, hYZ, hZ, u, v, hNotReachable, hLink⟩ :=
    WilliamsonShmoys.planar_component_link_exists Y hV hY hDisconnected
  obtain ⟨iZ, hDrop⟩ :=
    WilliamsonShmoys.component_count_decreases_after_link
      Y Z iY hYZ u v hNotReachable hLink
  exact ⟨Z, iZ, hYZ, hZ, hDrop⟩