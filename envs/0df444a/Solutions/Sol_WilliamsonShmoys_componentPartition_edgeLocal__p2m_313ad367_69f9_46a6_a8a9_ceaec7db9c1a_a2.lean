-- Prove2me | solution 1 for WilliamsonShmoys.componentPartition_edgeLocal__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:15:25.763425+00:00
-- url     : https://prove2.me/submissions/bc188e49-a3f3-4497-abb5-04f344103fd1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_componentPartition_core__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
import Theorems.Thm_WilliamsonShmoys_componentPartition_count__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) ∧
      (∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) := by
  letI : DecidableRel L.Adj := dL
  obtain ⟨C, hnonempty, hcover, hdisjoint, hconnected, hedge⟩ :=
    WilliamsonShmoys.componentPartition_core__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1 L dL
  obtain ⟨hcard, hsum⟩ :=
    WilliamsonShmoys.componentPartition_count__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
      L dL hconn hn C hnonempty hcover hdisjoint hconnected
  exact ⟨C, hcard, hnonempty, hcover, hdisjoint, hsum, hconnected, hedge⟩