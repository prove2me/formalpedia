-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:54:27.297479+00:00
-- url     : https://prove2.me/submissions/092b8034-c8aa-4bd1-a273-1ede6e96ae75

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_extremal_planar_supergraph_for_edge_count_26473918
import Theorems.Thm_WilliamsonShmoys_extremal_drawable_graph_has_euler_edge_count_26473918

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNdraw, hNmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_extremal_planar_supergraph_for_edge_count_26473918
      M hMdraw hCard
  exact ⟨N, hMN, hNdraw,
    WilliamsonShmoys.extremal_drawable_graph_has_euler_edge_count_26473918
      N hNdraw hCard hNmax⟩