-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:15:19.187528+00:00
-- url     : https://prove2.me/submissions/9b8e5320-87f9-4f1d-b3a2-bdda183ca050

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_induced_edge_bound_retry3
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_induced_subgraphs_retry3
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  apply WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs_retry3 H hV
  intro S hS hconn
  exact WilliamsonShmoys.planar_drawing_connected_induced_edge_bound_retry3
    H S hS hconn hH