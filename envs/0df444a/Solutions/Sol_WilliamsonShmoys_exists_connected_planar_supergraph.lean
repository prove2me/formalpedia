-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_planar_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:16:07.792769+00:00
-- url     : https://prove2.me/submissions/6efc5c11-af56-478c-923b-081cba54cd91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_edge_step
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_extension_of_disconnected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by
  exact WilliamsonShmoys.exists_connected_supergraph_of_edge_step
    (P := WilliamsonShmoys.HasPlanarDrawingOn) H hH
    (by
      intro G hHG hG hDisconnected
      exact WilliamsonShmoys.exists_planar_edge_extension_of_disconnected
        G hG hV hDisconnected)