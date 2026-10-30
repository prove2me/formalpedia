-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_exact_edge_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:58:40.010989+00:00
-- url     : https://prove2.me/submissions/78097103-be3d-4aba-8fcf-24c3b9899d70

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_dd73cac9_b90d_44a4_8977_1c0859414274
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_dd73cac9_b90d_44a4_8977_1c0859414274 H hH
  have hKcount :=
    WilliamsonShmoys.maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274
      K hKplanar hCard hKmax
  exact ⟨K, hHK, hKplanar, hKcount⟩