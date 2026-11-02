-- Prove2me | solution 2 for WilliamsonShmoys.planarDisconnectedComponentPartitionCounts__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:02:39.522402+00:00
-- url     : https://prove2.me/submissions/63238c25-2b55-4c86-a1a8-67091791fd54

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_componentPartition_edgeLocal__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
import Theorems.Thm_WilliamsonShmoys_inducedEdgeCount_edgeLocal_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = L.edgeFinset.card ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) ∧
      (∀ s ∈ C, edgeCount s = (L.induce (↑s : Set V)).edgeFinset.card) := by
  classical
  letI : DecidableRel L.Adj := dL
  obtain ⟨C, hCcard, hCnonempty, hCcover, hCdisjoint, hCvertices,
      hCconnected, hCedgeLocal⟩ :=
    WilliamsonShmoys.componentPartition_edgeLocal__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
      L dL hconn hn
  let edgeCount : Finset V → Nat :=
    fun s => (L.induce (↑s : Set V)).edgeFinset.card
  refine ⟨C, edgeCount, hCcard, hCnonempty, hCcover, hCdisjoint,
    hCvertices, ?_, hCconnected, ?_⟩
  · simpa [edgeCount] using
      (WilliamsonShmoys.inducedEdgeCount_edgeLocal_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
        L dL C hCcover hCdisjoint hCedgeLocal)
  · intro s hs
    rfl