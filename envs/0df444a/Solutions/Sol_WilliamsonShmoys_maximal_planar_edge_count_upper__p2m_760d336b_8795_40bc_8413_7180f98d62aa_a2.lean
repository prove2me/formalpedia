-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:26:11.802992+00:00
-- url     : https://prove2.me/submissions/f78de409-334b-4fc7-a060-3e0e0fb89a8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_ddd64127_46c6_4ff5_ad6f_47496ad35234_a2
import Mathlib

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    H.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, dK, hsub, hcardK⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_ddd64127_46c6_4ff5_ad6f_47496ad35234_a2
      H dH hH hcard
  letI : DecidableRel K.Adj := dK
  calc
    H.edgeFinset.card <= K.edgeFinset.card := Finset.card_le_card hsub
    _ = 3 * Fintype.card V - 6 := hcardK