-- Prove2me | solution 1 for PadbergRao.OddCut.min_tree_edge_min_odd_pair_cut
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:54:50.292266+00:00
-- url     : https://prove2.me/submissions/a2b6d9a0-918e-4bed-83c0-ae2e9cbe36b7

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_PadbergRao_OddCut_IsMinOddPairCut
import Definitions.Def_PadbergRao_OddCut_IsOddCutTree

open Finset
open PadbergRao.OddCut

set_option autoImplicit false

/-- A lightest edge of a terminal cut-tree gives a lightest terminal-separating cut. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (_hc_symm : ∀ i j, c i j = c j i) (_hc_nonneg : ∀ i j, 0 ≤ c i j)
    (odd : Finset V) (_hodd_ne : odd.Nonempty) (_hodd_even : Even odd.card)
    (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd})
    (hT : IsOddCutTree c odd H π)
    (r s : {v // v ∈ odd}) (hrs : H.Adj r s)
    (hmin : ∀ r' s' : {v // v ∈ odd}, H.Adj r' s' →
      treeEdgeWeight c H π r s ≤ treeEdgeWeight c H π r' s') :
    IsMinOddPairCut c odd (shore H π r s) := by
  classical
  have hbridge := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.1.isAcyclic hrs
  have hnreach : ¬ (H.deleteEdges {s(r, s)}).Reachable r s := hbridge
  have hrshore : (r : V) ∈ shore H π r s := by
    simp [shore, subtree, hT.2.1 r]
  have hsshore : (s : V) ∉ shore H π r s := by
    simpa [shore, subtree, hT.2.1 s] using hnreach
  refine ⟨⟨r, r.property, s, s.property, hrshore, hsshore⟩, ?_⟩
  intro U hU
  obtain ⟨p, hp, q, hq, hpU, hqU⟩ := hU
  obtain ⟨walk⟩ := hT.1.connected (⟨p, hp⟩ : {v // v ∈ odd}) ⟨q, hq⟩
  obtain ⟨d, _, hdU, hdU'⟩ := walk.exists_boundary_dart
    {v : {v // v ∈ odd} | (v : V) ∈ U} hpU hqU
  exact (hmin d.fst d.snd d.adj).trans (hT.2.2 d.fst d.snd d.adj U hdU hdU')
