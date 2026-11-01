-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:35.092138+00:00
-- url     : https://prove2.me/submissions/a8a7dcce-fb46-479a-9957-1fc98758f38f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_88a12398_1857_4cda_a49a_bb014d1d3fb8_a3
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall N : SimpleGraph V,
      (forall {u v : V}, M.Adj u v -> N.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     3 * Fintype.card V - 6 <= M.edgeFinset.card) := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  obtain ⟨N, hMN, hN, hedge⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_88a12398_1857_4cda_a49a_bb014d1d3fb8_a3
      M hM hcard
  have hEq : N = M := hmax N hMN hN
  cases hEq
  exact hedge