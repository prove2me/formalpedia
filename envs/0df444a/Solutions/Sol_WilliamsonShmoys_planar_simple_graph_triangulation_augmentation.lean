-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_triangulation_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:54:54.232962+00:00
-- url     : https://prove2.me/submissions/e686c38e-4135-4bad-8c6b-c588b46d1dea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_triangulation_augmentation_exists_edge_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_triangulation_augmentation_maximal_graph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hHK, hDraw, hMax⟩ :=
    WilliamsonShmoys.planar_simple_graph_triangulation_augmentation_exists_edge_maximal_supergraph
      H hH
  exact ⟨K, hHK,
    WilliamsonShmoys.planar_simple_graph_triangulation_augmentation_maximal_graph_edge_count
      K hDraw hMax hCard⟩
