-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:42.555219+00:00
-- url     : https://prove2.me/submissions/5cece465-d02b-45f6-9326-9d7a1b487b75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      (∀ u v, M.Adj u v → N.Adj u v) → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hN, hMN, hNmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
      M hM
  have hNM : N = M := hmax N hN hMN
  have hcount :=
    WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
      N hN hNmax hcard
  rw [hNM] at hcount
  omega