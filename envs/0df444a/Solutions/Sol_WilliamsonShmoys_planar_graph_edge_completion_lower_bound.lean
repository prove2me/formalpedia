-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_completion_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:56:55.389807+00:00
-- url     : https://prove2.me/submissions/01bf9645-4671-49e9-9a8c-c7ddcfc1398a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_completion_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_graph_edge_completion_maximal_extension M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_graph_edge_lower_bound N hV hN hmax⟩