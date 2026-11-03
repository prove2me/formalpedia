-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:37:38.700493+00:00
-- url     : https://prove2.me/submissions/959485c0-9d43-4114-9d6c-dea4cda3262c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1 M hMdraw
  exact WilliamsonShmoys.planar_edge_bound_of_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1 M N hMN hNdraw hmax hcard