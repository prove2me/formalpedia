-- Prove2me | solution 1 for WilliamsonShmoys.planarEdgeBound__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:04:07.262763+00:00
-- url     : https://prove2.me/submissions/8cd5f973-f83d-4469-86ef-a4568ce1937c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarEdgeBound_connected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
import Theorems.Thm_WilliamsonShmoys_planarEdgeBound_disconnected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel L.Adj := dL
  by_cases hconn : L.Connected
  · exact WilliamsonShmoys.planarEdgeBound_connected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
      L dL hL hconn hn
  · exact WilliamsonShmoys.planarEdgeBound_disconnected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
      L dL hL hconn hn