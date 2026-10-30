-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:00:05.595003+00:00
-- url     : https://prove2.me/submissions/8ea0b267-88c2-46b9-9c6d-21856e08ca9e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_planar_edge_count
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_extension
      K hV hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_planar_edge_count
      L hV hL hMax⟩