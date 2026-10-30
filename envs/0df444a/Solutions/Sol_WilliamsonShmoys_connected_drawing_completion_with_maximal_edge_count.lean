-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_completion_with_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:16:15.733588+00:00
-- url     : https://prove2.me/submissions/ed0a1239-2aa5-446b-900c-aa91564933bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_extension_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_maximal_edge_count_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_extension_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce K hK
  have hCount :=
    WilliamsonShmoys.edge_maximal_planar_graph_has_maximal_edge_count_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce H hH hCard hMaximal
  exact ⟨H, hKH, hH, hCount⟩