-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_count__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:45:52.012526+00:00
-- url     : https://prove2.me/submissions/da6f5a98-6481-4350-965d-6053811c53f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N)
    (hV : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  exact Nat.le_antisymm
    (WilliamsonShmoys.planar_edge_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1 N hN hV)
    (WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1 N hN hmax hV)