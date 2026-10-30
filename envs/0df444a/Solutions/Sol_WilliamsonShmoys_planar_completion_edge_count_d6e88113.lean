-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count_d6e88113
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:21:32.764989+00:00
-- url     : https://prove2.me/submissions/9103efd5-fa3a-4fea-bc81-d4c55629aeac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_e4624ca0

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, HasPlanarDrawingOn L ∧ K ≤ L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hL, hKL, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph K hdraw
  refine ⟨L, hL, hKL, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count_e4624ca0 L hL hmax hV