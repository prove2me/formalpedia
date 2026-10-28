-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_edge_bound_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:15:46.539716+00:00
-- url     : https://prove2.me/submissions/92850957-ed1d-4ccb-8246-4083b16a83ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_extension_20261026
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_spanning_triangulation_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hplanarH, hsub, hcard⟩ :=
    WilliamsonShmoys.connected_planar_drawing_triangulation_extension_20261026
      K hconn hK hV
  exact WilliamsonShmoys.edge_bound_of_spanning_triangulation_20261026
    K hV H hsub hcard