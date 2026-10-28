-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_augmentation_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:11:35.133513+00:00
-- url     : https://prove2.me/submissions/9dc2c852-f265-4fe6-908f-0a664f98a3e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_8a5c5037_77da_430d_9643_dec01e9a1ed1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_bound_8a5c5037_77da_430d_9643_dec01e9a1ed1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_8a5c5037_77da_430d_9643_dec01e9a1ed1 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_supergraph_edge_bound_8a5c5037_77da_430d_9643_dec01e9a1ed1 K hK hV hmax⟩