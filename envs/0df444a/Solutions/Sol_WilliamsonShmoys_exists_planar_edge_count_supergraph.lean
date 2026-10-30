-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_count_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:53:53.35741+00:00
-- url     : https://prove2.me/submissions/aade2e76-b27b-4703-940b-aa89a0d3a4bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_200a044f_248b_4fd0_bcd3_c7e9d499ee78
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_200a044f_248b_4fd0_bcd3_c7e9d499ee78

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_200a044f_248b_4fd0_bcd3_c7e9d499ee78 L hL
  refine ⟨T, hLT, hT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_200a044f_248b_4fd0_bcd3_c7e9d499ee78 T hT hCard hmax