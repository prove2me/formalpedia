-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:34:57.584813+00:00
-- url     : https://prove2.me/submissions/d5763dbc-2b62-47cb-85b0-e88f035f1793

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2_maximal_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L ≤ M ∧
      3 * (Fintype.card V : Int) - 6 <= (M.edgeSet.ncard : Int) := by
  obtain ⟨M, hM, hLM, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_extension L hL hCard
  exact ⟨M, hM, hLM,
    WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_edge_bound
      M hM hCard hMax⟩