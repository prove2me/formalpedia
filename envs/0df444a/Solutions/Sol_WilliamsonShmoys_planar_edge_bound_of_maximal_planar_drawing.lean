-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_maximal_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:45:35.189227+00:00
-- url     : https://prove2.me/submissions/dde12493-2b61-41d6-9344-f1924a303b32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension_for_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hEq⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound
      H hV hHplanar
  have hKH : K = H := hmax K hHK hKplanar
  rw [hKH] at hEq
  omega