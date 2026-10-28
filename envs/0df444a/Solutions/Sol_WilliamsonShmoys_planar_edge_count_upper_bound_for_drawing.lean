-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_for_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:59:23.199288+00:00
-- url     : https://prove2.me/submissions/29b68619-f7de-47df-80e2-a5b222e2c19b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_connected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_induced_subgraphs

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs K hV
  intro S hS hconn
  have hdraw := WilliamsonShmoys.planar_drawingOn_induce K hK S
  have hcard : 3 ≤ Fintype.card {v // v ∈ S} := by
    simpa using hS
  have hbound :=
    WilliamsonShmoys.planar_edge_count_upper_bound_for_connected_drawing
      (K.induce (↑S : Set V)) hdraw hconn hcard
  simpa using hbound