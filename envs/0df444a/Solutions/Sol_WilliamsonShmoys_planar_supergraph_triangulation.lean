-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:26:06.902682+00:00
-- url     : https://prove2.me/submissions/6caefae5-5050-4507-9c34-506322220858

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_exists_edge_maximal_supergraph_20261026
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_edge_count_20261026

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_exists_edge_maximal_supergraph_20261026 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_20261026 L hL hV hmax⟩