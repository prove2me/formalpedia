-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:16:16.959067+00:00
-- url     : https://prove2.me/submissions/7e43ed66-d6ba-4e49-8431-211a469aa6f4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_supergraph

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) : 3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hEdges⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulation_supergraph L hL hCard
  have hEq : M = L := hMax M hLM hM
  rw [hEq] at hEdges
  omega