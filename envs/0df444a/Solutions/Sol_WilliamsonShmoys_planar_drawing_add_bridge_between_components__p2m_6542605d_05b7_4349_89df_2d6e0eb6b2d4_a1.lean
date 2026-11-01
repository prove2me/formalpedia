-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_bridge_between_components__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:01.199398+00:00
-- url     : https://prove2.me/submissions/dfa18ef5-a47c-47cb-aa6a-deadffc1be81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_graph_has_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_across_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn K)
    (hdisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
      HasPlanarDrawingOn L := by
  obtain ⟨A, B, hA, hB, hdisjoint, hcover, hcut⟩ :=
    WilliamsonShmoys.disconnected_graph_has_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1 K hdisconnected
  exact WilliamsonShmoys.planar_drawing_add_bridge_across_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
    K hplanar A B hA hB hdisjoint hcover hcut