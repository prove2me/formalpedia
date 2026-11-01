-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_of_drawing__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:10:27.713826+00:00
-- url     : https://prove2.me/submissions/8bfff1a6-1edd-438b-9dd8-be7cf9c6bd95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    W.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hH, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2 W hW
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
      H hH hmax hcard
  calc
    W.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hsub
    _ ≤ 3 * Fintype.card V - 6 := hbound