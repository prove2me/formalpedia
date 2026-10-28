-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_face_count_c76468fe
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:42:57.872287+00:00
-- url     : https://prove2.me/submissions/1cbc63e2-c4f8-4b8c-b1cc-a8d8e83499e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion_for_maximal_planar_count_92703542_9701_452c_b6a8_363f18bf7214

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 /\
      3 * f = 2 * H.edgeSet.ncard := by
  have hCompletion := WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximal_planar_count_92703542_9701_452c_b6a8_363f18bf7214 H hH hCard
  let K := hCompletion.choose
  have hHK : H <= K := hCompletion.choose_spec.1
  have hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K := hCompletion.choose_spec.2.1
  have hcount : K.edgeSet.ncard + 6 = 3 * Fintype.card V := hCompletion.choose_spec.2.2
  have hEq : K = H := hmax K hHK hKdraw
  rw [hEq] at hcount
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega