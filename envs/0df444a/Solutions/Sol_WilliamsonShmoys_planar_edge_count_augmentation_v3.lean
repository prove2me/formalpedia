-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_augmentation_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:23:46.269302+00:00
-- url     : https://prove2.me/submissions/17a15422-3e42-492a-8fa4-fa7f1be0da5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_local_growth_implies_connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_graph_has_strict_planar_growth

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  have hV2 : 2 <= Fintype.card V := by omega
  apply WilliamsonShmoys.planar_supergraph_local_growth_implies_connected K hK
  intro G hKG hG hDisconnected
  exact WilliamsonShmoys.planar_drawing_disconnected_graph_has_strict_planar_growth
    G hV2 hG hDisconnected