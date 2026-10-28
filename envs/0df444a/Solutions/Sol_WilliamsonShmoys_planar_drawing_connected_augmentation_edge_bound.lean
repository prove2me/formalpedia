-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:53:40.473474+00:00
-- url     : https://prove2.me/submissions/339453f9-9517-462a-b689-ccc90290e124
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hcount, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_extension G hG hV
  have hconn := WilliamsonShmoys.edge_maximal_planar_graph_connected H hH hV hmax
  exact ⟨H, hGH, hcount, hconn, hH⟩