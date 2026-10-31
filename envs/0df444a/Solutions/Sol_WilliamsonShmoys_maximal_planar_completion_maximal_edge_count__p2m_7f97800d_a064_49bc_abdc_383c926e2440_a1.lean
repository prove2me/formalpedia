-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_maximal_edge_count__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:36.806623+00:00
-- url     : https://prove2.me/submissions/50616791-bfd3-485e-b8c6-0f6dc1ff55ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count__p2m_078165f8_2282_4c2b_9ab6_7e9aed87e1a3_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmaximal : forall N : SimpleGraph V, LE.le M N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N = M)
    (hV : 3 <= Fintype.card V) : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hNplanar, hNcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_078165f8_2282_4c2b_9ab6_7e9aed87e1a3_a1
      M hMplanar hV
  have hNM : N = M := hmaximal N hMN hNplanar
  simpa [hNM] using hNcount