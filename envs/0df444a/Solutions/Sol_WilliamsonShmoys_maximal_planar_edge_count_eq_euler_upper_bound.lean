-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq_euler_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:45:22.957165+00:00
-- url     : https://prove2.me/submissions/80ec68f0-1a1b-4b17-ba65-9dc44be32092

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler_formula_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a H hH
  have hKeq :=
    WilliamsonShmoys.maximal_planar_edge_count_eq_euler_formula_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a
      K ⟨hKdraw, hKmax⟩ hCard
  have hsub : H.edgeSet ⊆ K.edgeSet := SimpleGraph.edgeSet_mono hHK
  have hncard : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hsub
  omega