-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_of_not_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:33:52.588813+00:00
-- url     : https://prove2.me/submissions/8902aee7-c07e-4cb0-ac7a-35d3d18ef813
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_nonempty_has_unreachable_pair
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable_vertices

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K ≠ H ∧ HasPlanarDrawingOn K := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_nonempty_has_unreachable_pair H hV hDisconnected
  exact WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices
    H hH u v huv