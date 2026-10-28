-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:58:12.052819+00:00
-- url     : https://prove2.me/submissions/04c43512-853f-4ec9-a57b-51b466afba79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_on_same_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKdraw, hKcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_on_same_vertices H hV hHdraw
  have hKH : K = H := hHmax K hHK hKdraw
  calc
    H.edgeSet.ncard = K.edgeSet.ncard := by rw [hKH]
    _ = 3 * Fintype.card V - 6 := hKcard
    _ ≤ 3 * Fintype.card V - 6 := le_rfl