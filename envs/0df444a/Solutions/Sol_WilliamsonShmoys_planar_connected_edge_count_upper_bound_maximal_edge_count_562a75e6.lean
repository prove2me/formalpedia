-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_count_upper_bound_maximal_edge_count_562a75e6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:46:29.297792+00:00
-- url     : https://prove2.me/submissions/5863efdb-2290-4e39-bcf4-ac41e5cc0791
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_7607aed3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (H.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hHK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_7607aed3 H hdraw hconn hV
  have hKH : K = H := hmax K hHK hKdraw
  rw [← hKH]
  exact le_of_eq hKcount