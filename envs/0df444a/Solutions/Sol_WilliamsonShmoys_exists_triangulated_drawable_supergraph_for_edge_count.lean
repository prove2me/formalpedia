-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_drawable_supergraph_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:08:33.650057+00:00
-- url     : https://prove2.me/submissions/fd5d6fb7-1b3a-4153-9369-0f1bcc5fc92b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_for_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  obtain ⟨T, hST, hTdraw, hTmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_for_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2 S hSdraw
  have hCount := WilliamsonShmoys.maximal_drawable_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2 T hTdraw hCard hTmax
  exact ⟨T, hST, hTdraw, hCount⟩