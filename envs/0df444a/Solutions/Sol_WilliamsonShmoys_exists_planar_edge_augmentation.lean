-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:16:43.061105+00:00
-- url     : https://prove2.me/submissions/bd439c74-08b2-4258-97e0-03322c54981b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_disconnected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  have hNonempty : 0 < Fintype.card V := by omega
  obtain ⟨u, v, hUnreachable⟩ :=
    WilliamsonShmoys.exists_unreachable_pair_of_disconnected G hNonempty hNotConnected
  obtain ⟨H, hStrict, _hBridge, hDrawing⟩ :=
    WilliamsonShmoys.planar_drawing_add_edge_between_unreachable G hG hUnreachable
  exact ⟨H, hStrict, hDrawing⟩