-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_ff2dc3a7_bc0c_4f6e_ac65_1b9f4eedc148_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:33:39.758623+00:00
-- url     : https://prove2.me/submissions/26b28c3b-47d5-4e45-a517-a746abc7d538

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard :=
  WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count M hCard hM
