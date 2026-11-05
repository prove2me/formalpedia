-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum_aggregate_arithmetic__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:23:45.510963+00:00
-- url     : https://prove2.me/submissions/e6ee8bba-d773-41f1-bb4f-b54c4320f4ac

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hmany : 2 <= C.card)
    (haggregate : N.edgeFinset.card + 3 * C.card <= 3 * Fintype.card V) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  omega
