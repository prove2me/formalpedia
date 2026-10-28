-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_from_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:38:01.888901+00:00
-- url     : https://prove2.me/submissions/d3bb96dd-7aa8-4803-91df-ca35e2a046c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_via_faces
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_via_euler

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hdrawH, hconn, hsub⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_via_faces G hdraw hV
  exact le_trans hsub
    (WilliamsonShmoys.connected_planar_drawing_edge_bound_via_euler H hdrawH hconn hV)