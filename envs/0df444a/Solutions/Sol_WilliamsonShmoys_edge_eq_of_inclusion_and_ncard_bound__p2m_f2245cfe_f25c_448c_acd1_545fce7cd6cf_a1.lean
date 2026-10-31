-- Prove2me | solution 1 for WilliamsonShmoys.edge_eq_of_inclusion_and_ncard_bound__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:53.625493+00:00
-- url     : https://prove2.me/submissions/d2ba74b4-de49-435a-8d6d-020a99cce758

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) : H = G := by
  classical
  have hsub : G.edgeSet ⊆ H.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact hGH he
  have hedges : G.edgeSet = H.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub hcard
  ext v w
  have hm : s(v, w) ∈ H.edgeSet ↔ s(v, w) ∈ G.edgeSet := by
    rw [hedges]
  simpa only [SimpleGraph.mem_edgeSet] using hm