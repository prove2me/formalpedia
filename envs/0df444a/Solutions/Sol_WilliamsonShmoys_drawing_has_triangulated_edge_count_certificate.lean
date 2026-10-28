-- Prove2me | solution 1 for WilliamsonShmoys.drawing_has_triangulated_edge_count_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:06:25.944562+00:00
-- url     : https://prove2.me/submissions/7c70dd4a-f83c-48f5-9ced-0d4a8d7ae4e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_has_planar_drawing_on_edge_count_le_three_card_sub_six
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ m f : Nat, G.edgeSet.ncard ≤ m ∧
      Fintype.card V + f = m + 2 ∧ 3 * f ≤ 2 * m := by
  have hEdge :=
    WilliamsonShmoys.has_planar_drawing_on_edge_count_le_three_card_sub_six G hG hCard
  refine ⟨3 * Fintype.card V - 6, 2 * Fintype.card V - 4, hEdge, ?_, ?_⟩
  · omega
  · omega