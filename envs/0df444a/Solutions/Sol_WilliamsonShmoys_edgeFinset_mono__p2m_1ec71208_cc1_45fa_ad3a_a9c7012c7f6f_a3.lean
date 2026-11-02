-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_mono__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:17.564482+00:00
-- url     : https://prove2.me/submissions/c05cec86-77e5-4135-a8ad-d556d11f935c

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G <= H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel H.Adj := Classical.decRel H.Adj
     G.edgeFinset.card <= H.edgeFinset.card) := by
  classical
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
