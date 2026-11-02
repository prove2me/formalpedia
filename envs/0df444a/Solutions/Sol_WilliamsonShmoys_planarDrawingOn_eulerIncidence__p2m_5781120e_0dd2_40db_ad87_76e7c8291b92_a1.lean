-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_eulerIncidence__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:51:55.992836+00:00
-- url     : https://prove2.me/submissions/5c83fe2d-e7cb-477a-ba07-1251c3f47270

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerFormula__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceIncidences__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ f i : ℕ,
      Fintype.card V + f = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 2 ∧
      2 * (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ≤ i ∧
      3 * f ≤ i := by
  letI : DecidableRel L.Adj := dL
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planarDrawingOn_eulerFormula__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
      L dL hL hconn
  obtain ⟨i, hEdges, hFaces⟩ :=
    WilliamsonShmoys.planarDrawingOn_faceIncidences__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
      L dL hL hconn hn f hEuler
  exact ⟨f, i, hEuler, hEdges, hFaces⟩