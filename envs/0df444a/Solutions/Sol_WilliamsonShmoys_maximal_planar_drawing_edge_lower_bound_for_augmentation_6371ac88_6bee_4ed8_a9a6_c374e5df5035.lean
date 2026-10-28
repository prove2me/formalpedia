-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:52:43.138084+00:00
-- url     : https://prove2.me/submissions/d1cefad2-a99b-4d6c-8790-1ac759b4cfb8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_planar_completion_with_edge_lower_bound
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  classical
  let completion :=
    WilliamsonShmoys.exists_planar_completion_with_edge_lower_bound H hV hH
  let K := Classical.choose completion
  have hprops := Classical.choose_spec completion
  have hHK : H <= K := hprops.1
  have hK : WilliamsonShmoys.HasPlanarDrawingOn K := hprops.2.1
  have hbound : 3 * Fintype.card V <= K.edgeSet.ncard + 6 := hprops.2.2
  have hKH : K <= H := hmax K hHK hK
  have hEq : H = K := le_antisymm hHK hKH
  simpa [hEq] using hbound