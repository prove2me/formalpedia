-- Prove2me | solution 1 for WilliamsonShmoys.planarDisconnectedComponentPartitionCounts__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:07:24.097714+00:00
-- url     : https://prove2.me/submissions/fdfbfbe9-0b87-44dc-834b-d9900e879f4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
import Theorems.Thm_WilliamsonShmoys_inducedEdgeCount_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1

set_option autoImplicit false

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
  obtain ⟨C, hCcard, hCnonempty, hCcover, hCdisjoint, hCvertices, hCconnected⟩ :=
    WilliamsonShmoys.componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
      L dL hconn hn
  let edgeCount : Finset V → Nat := fun s => (L.induce (↑s : Set V)).edgeFinset.card
  refine ⟨C, edgeCount, hCcard, hCnonempty, hCcover, hCdisjoint, hCvertices, ?_, hCconnected, ?_⟩
  · simpa [edgeCount] using
      (WilliamsonShmoys.inducedEdgeCount_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
        L dL C hCcover hCdisjoint)
  · intro s hs
    rfl
