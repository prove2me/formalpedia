-- Prove2me | solution 2 for WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:23:30.698983+00:00
-- url     : https://prove2.me/submissions/ce37bf81-987c-4a81-8bd0-97e321d89c96

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (L : SimpleGraph V) (dL : DecidableRel L.Adj)
        (hL : HasPlanarDrawingOn L)
        (hconn : ¬ L.Connected),
        (letI : DecidableRel L.Adj := dL;
        ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
          2 ≤ C.card ∧
          (∀ s ∈ C, s.Nonempty) ∧
          (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
          (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
          (∑ s ∈ C, s.card) = Fintype.card V ∧
          (∑ s ∈ C, edgeCount s) = L.edgeFinset.card ∧
          (∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card))) := by
  classical
  intro h
  letI : DecidableRel ((⊥ : SimpleGraph Empty).Adj) := Classical.decRel _
  have hL : HasPlanarDrawingOn (⊥ : SimpleGraph Empty) := by
    refine ⟨(fun v : Empty => nomatch v), (fun u : Empty => nomatch u), ?_, ?_, ?_⟩
    · intro x
      cases x
    · intro u
      cases u
    · intro u
      cases u
  have hconn : ¬ (⊥ : SimpleGraph Empty).Connected := by
    intro hc
    exact hc.nonempty.elim (fun v => nomatch v)
  have hEmpty := h (V := Empty) (L := (⊥ : SimpleGraph Empty)) ‹DecidableRel _› hL hconn
  rcases hEmpty with ⟨C, edgeCount, hC, _⟩
  have hle : C.card ≤ 1 := by
    calc
      C.card ≤ Finset.univ.card := Finset.card_le_univ C
      _ = 1 := by simp
  omega