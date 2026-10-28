-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_with_fewer_edges_can_be_augmented
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:37:28.082195+00:00
-- url     : https://prove2.me/submissions/edc2b29a-3931-4945-9c36-23720a2e1967
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_edge_count_lower_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hLow : N.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ Q : SimpleGraph V,
      N ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q ≠ N := by
  obtain ⟨Q, hNQ, hQ, hMax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph N hN
  have hBound :=
    WilliamsonShmoys.planar_drawingOn_maximal_edge_count_lower_bound Q hCard hQ hMax
  by_cases hEq : Q = N
  · subst Q
    omega
  · exact ⟨Q, hNQ, hQ, hEq⟩