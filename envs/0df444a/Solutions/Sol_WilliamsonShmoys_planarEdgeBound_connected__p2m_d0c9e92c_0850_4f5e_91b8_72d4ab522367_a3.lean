-- Prove2me | solution 1 for WilliamsonShmoys.planarEdgeBound_connected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:29:20.976133+00:00
-- url     : https://prove2.me/submissions/723687a0-ee15-411f-b595-8f827dc49979
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_eulerIncidence_edge_bound__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerIncidence__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  rcases WilliamsonShmoys.planarDrawingOn_eulerIncidence__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
      L dL hL hconn hn with ⟨f, i, hEuler, hEdgeInc, hFaceInc⟩
  exact WilliamsonShmoys.eulerIncidence_edge_bound__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
    L dL f i hn hEuler hEdgeInc hFaceInc