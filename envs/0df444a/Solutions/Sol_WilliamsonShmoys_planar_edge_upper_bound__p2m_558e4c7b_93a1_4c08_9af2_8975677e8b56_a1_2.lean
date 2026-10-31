-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:22:24.663433+00:00
-- url     : https://prove2.me/submissions/82519552-b85c-4687-ba32-f9168cadae99

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 L hL hCard
