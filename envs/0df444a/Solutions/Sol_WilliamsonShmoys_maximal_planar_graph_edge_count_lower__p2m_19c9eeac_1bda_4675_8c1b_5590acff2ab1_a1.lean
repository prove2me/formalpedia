-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:53:14.524573+00:00
-- url     : https://prove2.me/submissions/79eab6db-01e4-46f7-bc4a-2d38c836d863

import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_9c1c6a07_df32_48f2_a3fa_6413055e7fe1_a1
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V)
    (hmax : forall S : SimpleGraph V, R <= S -> HasPlanarDrawingOn S -> S = R) :
    3 * Fintype.card V - 6 <= R.edgeSet.ncard := by
  obtain ⟨S, hRS, hSDraw, hSedges⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_extension__p2m_9c1c6a07_df32_48f2_a3fa_6413055e7fe1_a1
      R hDraw hV
  have hEq : S = R := hmax S hRS hSDraw
  rw [hEq] at hSedges
  omega