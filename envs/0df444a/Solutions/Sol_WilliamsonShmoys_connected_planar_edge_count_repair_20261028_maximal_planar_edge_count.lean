-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_repair_20261028_maximal_planar_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:53:22.89503+00:00
-- url     : https://prove2.me/submissions/80abeb4f-901f-4705-ba7c-10f7783f9c8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_edgeSet_ncard_le_three_mul_card_sub_six
import Theorems.Thm_maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : forall L : SimpleGraph V, G <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = G)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    planar_drawing_edgeSet_ncard_le_three_mul_card_sub_six G hDraw hCard
  have hLower :=
    maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six G hDraw hMax hCard
  omega