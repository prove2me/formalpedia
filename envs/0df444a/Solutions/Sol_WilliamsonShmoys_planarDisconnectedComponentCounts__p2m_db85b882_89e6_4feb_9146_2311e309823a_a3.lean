-- Prove2me | solution 1 for WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:55:59.649485+00:00
-- url     : https://prove2.me/submissions/850e3203-72ff-45ce-a57f-c95c6f5a17c8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDisconnectedComponentPartitionCounts__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
import Theorems.Thm_WilliamsonShmoys_connectedPlanarInducedEdgeBound__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ∧
      (∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card) := by
  letI : DecidableRel L.Adj := dL
  obtain ⟨C, edgeCount, hcard, hnonempty, hcover, hdisjoint, hsize, hedges,
      hconnected, hcount⟩ :=
    WilliamsonShmoys.planarDisconnectedComponentPartitionCounts__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
      L dL hconn hn
  refine ⟨C, edgeCount, hcard, hnonempty, hcover, hdisjoint, hsize, hedges, ?_⟩
  intro s hs
  rw [hcount s hs]
  exact WilliamsonShmoys.connectedPlanarInducedEdgeBound__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
    L dL hL s (hconnected s hs)