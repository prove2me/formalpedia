-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_strict_extension__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:35:42.981043+00:00
-- url     : https://prove2.me/submissions/58e29f95-775a-4ced-a803-4508b767051a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_disconnected_vertices__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hdisc : ¬ G.Connected) : ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H := by
  obtain ⟨u, v, huv, hnotReachable⟩ :=
    WilliamsonShmoys.disconnected_vertices__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1 G hcard hdisc
  obtain ⟨H, hGH, hAdded, hH⟩ :=
    WilliamsonShmoys.planar_add_edge_between_components__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
      G hG u v hnotReachable
  exact ⟨H, hGH, hH⟩