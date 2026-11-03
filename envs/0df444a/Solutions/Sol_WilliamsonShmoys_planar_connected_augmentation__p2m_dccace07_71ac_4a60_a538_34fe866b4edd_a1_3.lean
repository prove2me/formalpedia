-- Prove2me | solution 3 for WilliamsonShmoys.planar_connected_augmentation__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:55:01.298148+00:00
-- url     : https://prove2.me/submissions/d394e1bf-8cb4-45e2-b999-57906f35e18d

import Theorems.Thm_WilliamsonShmoys_connected_planar_augmentation

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.connected_planar_augmentation G hCard hDraw