-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_eulerFormula__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:07:00.899816+00:00
-- url     : https://prove2.me/submissions/2fa315dd-ab1b-4b59-9b34-1dd600ad8e09

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_edgeFinset_card_lower_bound__p2m_bd7293c6_e84f_4a76_8bde_2e7b0da2a7be_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 2 := by
  letI : DecidableRel L.Adj := dL
  have hlower := WilliamsonShmoys.connected_edgeFinset_card_lower_bound__p2m_bd7293c6_e84f_4a76_8bde_2e7b0da2a7be_a1 L dL hconn
  refine ⟨L.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega