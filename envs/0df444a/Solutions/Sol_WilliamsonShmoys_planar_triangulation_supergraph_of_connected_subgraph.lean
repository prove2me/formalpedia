-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_of_connected_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:20:26.254207+00:00
-- url     : https://prove2.me/submissions/82f1a29e-bd1e-4a24-825c-bc7cdf06c1db

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_by_inclusion_79bba284
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_79bba284

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J K : SimpleGraph V)
    (hJK : J.edgeSet ⊆ K.edgeSet)
    (hConn : J.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximal_by_inclusion_79bba284 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count_79bba284 L hV hL hMax⟩