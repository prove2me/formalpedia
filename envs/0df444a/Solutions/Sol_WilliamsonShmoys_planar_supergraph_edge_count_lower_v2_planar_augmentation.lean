-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_planar_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:13:34.619713+00:00
-- url     : https://prove2.me/submissions/c39a42bd-cae6-4f05-88e4-43ffefec4d1b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M ≤ N ∧
      3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by
  obtain ⟨N, hN, hMN, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_v2 M hM
  exact ⟨N, hN, hMN,
    WilliamsonShmoys.maximal_planar_graph_edge_count_lower_v2 N hN hMax hCard⟩