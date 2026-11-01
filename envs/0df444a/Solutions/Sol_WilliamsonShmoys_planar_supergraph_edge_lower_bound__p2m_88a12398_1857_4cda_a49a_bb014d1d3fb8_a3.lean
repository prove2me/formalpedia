-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_88a12398_1857_4cda_a49a_bb014d1d3fb8_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:31:20.080359+00:00
-- url     : https://prove2.me/submissions/ed1fe1df-b0d5-41d5-8f95-4522b7698586
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_extension__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_lower_bound__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      (forall {u v : V}, M.Adj u v -> N.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       3 * Fintype.card V - 6 <= N.edgeFinset.card) := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
      M hM hcard
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
    N hN hcard hMax