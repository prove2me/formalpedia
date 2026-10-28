-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_eb9e91c8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:08:54.933727+00:00
-- url     : https://prove2.me/submissions/c66975f8-3926-449e-af38-1ac4069e2198
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hMax : forall K : SimpleGraph V,
      H <= K -> HasPlanarDrawingOn K -> K = H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hCount⟩ :=
    planar_drawing_triangulated_supergraph_exists H hH hCard
  have hEq : K = H := hMax K hHK hK
  simpa [hEq] using hCount