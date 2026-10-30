-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:48:42.170064+00:00
-- url     : https://prove2.me/submissions/27680958-4f5d-4424-b190-44d7abdc3274

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
import Theorems.Thm_WilliamsonShmoys_edge_count_monotone_4881293e_7bf5_4184_9f0b_57a8f75b0b6d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨T, hLT, hT⟩ :=
    WilliamsonShmoys.planar_extension_4881293e_7bf5_4184_9f0b_57a8f75b0b6d L hL hV
  exact WilliamsonShmoys.edge_count_monotone_4881293e_7bf5_4184_9f0b_57a8f75b0b6d L T hLT hT