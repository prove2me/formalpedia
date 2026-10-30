-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_on
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:02:55.46259+00:00
-- url     : https://prove2.me/submissions/786b6e5e-8d85-4c05-b870-502190024b5b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_le_three_n_sub_six_from_planar_drawing
import Theorems.Thm_WilliamsonShmoys_planar_graph_with_fewer_edges_can_be_augmented

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V,
      N ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.edge_count_le_three_n_sub_six_from_planar_drawing N hN hCard
  have hnot : ¬ N.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    intro hlt
    obtain ⟨Q, hNQ, hQ, hQne⟩ :=
      WilliamsonShmoys.planar_graph_with_fewer_edges_can_be_augmented N hN hCard hlt
    exact hQne (hMax Q hNQ hQ)
  omega