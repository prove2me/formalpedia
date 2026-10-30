-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulation_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:56:34.116623+00:00
-- url     : https://prove2.me/submissions/e99bcc12-b5f8-41cd-a720-eb0c99634230

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count_c4011bda
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_c4011bda
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_c4011bda L hL
  exact ⟨T, hLT, hT,
    WilliamsonShmoys.maximal_planar_supergraph_edge_count_c4011bda T hT hmax hCard⟩