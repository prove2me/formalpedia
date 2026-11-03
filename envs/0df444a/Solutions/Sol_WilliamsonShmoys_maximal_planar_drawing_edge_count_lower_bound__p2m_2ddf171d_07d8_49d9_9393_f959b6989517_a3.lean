-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:41:05.913324+00:00
-- url     : https://prove2.me/submissions/1b41f0dc-245e-4468-824e-2548ec6877af

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_27e53667_a776_4b32_8a84_50a3a7284dfa_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M)
    (hMmax : forall N : SimpleGraph V, M <= N ->
      HasPlanarDrawingOn N -> N <= M) :
    3 * Fintype.card V <=
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card) + 6 := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hex :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_27e53667_a776_4b32_8a84_50a3a7284dfa_a1
      M hcard hMdraw
  cases hex with
  | intro N hN =>
    cases hN with
    | intro hMN hN =>
      cases hN with
      | intro hNdraw hCount =>
        have hNM : N <= M := hMmax N hMN hNdraw
        have hEq : N = M := le_antisymm hNM hMN
        rw [hEq] at hCount
        omega