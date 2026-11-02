-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_max_edge_supergraph__p2m_ec2412ad_17a6_418f_a499_5de65dee72a0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:35:07.289205+00:00
-- url     : https://prove2.me/submissions/c4719c59-c18d-4fb2-8153-bb89f3842fa8

import Mathlib

open Finset Fintype

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ N' : SimpleGraph V, M ≤ N' → P N' →
        (letI : DecidableRel N'.Adj := Classical.decRel N'.Adj; N'.edgeFinset.card) ≤
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj; N.edgeFinset.card) := by
  classical
  let S : Set (SimpleGraph V) := {N | M ≤ N ∧ P N}
  have hSfinite : S.Finite := Set.toFinite S
  let s := hSfinite.toFinset
  have hs : s.Nonempty := by
    refine ⟨M, ?_⟩
    simp [s, S, hM]
  obtain ⟨N, hNs, hmax⟩ :=
    Finset.exists_max_image s (fun G : SimpleGraph V => G.edgeFinset.card) hs
  have hN : M ≤ N ∧ P N := by
    simpa [s, S] using hNs
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro N' hMN' hPN'
  have hN's : N' ∈ s := by simp [s, S, hMN', hPN']
  simpa using hmax N' hN's
