-- Prove2me | solution 2 for WilliamsonShmoys.planarEdgeBound_connected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:56:22.046428+00:00
-- url     : https://prove2.me/submissions/26649fb5-f4df-4bd3-a60c-821d44b70e10

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_connected

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
  letI : DecidableRel L.Adj := dL
  have h := WilliamsonShmoys.planar_drawing_edge_bound_connected L hL hconn hn
  rw [← Set.fintypeCard_eq_ncard, ← L.edgeFinset_card] at h
  omega
