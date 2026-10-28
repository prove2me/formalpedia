-- Prove2me | solution 1 for WilliamsonShmoys.euler_certificate_monotone_edge_bound__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:29:03.79591+00:00
-- url     : https://prove2.me/submissions/a9183053-b323-4ef0-b083-6309b2c871ef

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hCard : 3 ≤ Fintype.card V)
    (hcert : ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEq, hBound⟩ := hcert
  have hEdges : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)
  omega