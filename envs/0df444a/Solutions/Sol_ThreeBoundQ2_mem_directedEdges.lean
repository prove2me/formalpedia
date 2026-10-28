-- Prove2me | solution 1 for ThreeBoundQ2.mem_directedEdges
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:43:32.328868+00:00
-- url     : https://prove2.me/submissions/5221fdb1-def4-459e-a4c6-b4a29038db26

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
import Definitions.Def_Sensitivity213303_TournamentHighRows


section
/-
Canonical numbering and actual tournament-degree bridge for the executable
q2 enumerator.  This connects combinatorial coverage to finite tournaments,
without replacing sensitivity charging by numerical assumptions.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2
open scoped Classical BigOperators



@[simp] theorem mem_edges {n : ℕ} (i j : Fin n) :
    (i,j) ∈ edges n ↔ i < j := by
  simp [edges]







theorem directedEdges_map {V : Type} (es : List (V × V)) (d : V × V → Bool) :
    directedEdges es (es.map d) = es.map (fun e => if d e then e.swap else e) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      change (if d e then e.swap else e) :: directedEdges es (es.map d) =
        (if d e then e.swap else e) :: es.map (fun e => if d e then e.swap else e)
      rw [ih]

theorem directedEdges_orientation {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    directedEdges (edges n) (orientationBits R) = (edges n).map (orientEdge R) := by
  unfold orientationBits
  rw [directedEdges_map]
  congr 1
  funext e
  simp [orientEdge]

















end ThreeBoundQ2





end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundQ2
end ThreeBoundQ2
open ThreeBoundQ2
open scoped Classical BigOperators

theorem solution {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hR : TournamentHighRows.IsTournament R) (v w : Fin n) :
    (v,w) ∈ directedEdges (edges n) (orientationBits R) ↔ R v w := by
  rw [directedEdges_orientation, List.mem_map]
  constructor
  · rintro ⟨⟨i,j⟩, he, hj⟩
    have hij := (mem_edges i j).1 he
    by_cases hr : R j i
    · simp only [orientEdge, hr, ↓reduceIte, Prod.swap, Prod.mk.injEq] at hj
      rcases hj with ⟨rfl,rfl⟩
      exact hr
    · simp only [orientEdge, hr, ↓reduceIte, Prod.mk.injEq] at hj
      rcases hj with ⟨rfl,rfl⟩
      exact (hR.orient _ _ (ne_of_lt hij)).2 hr
  · intro hvw
    have hvwne : v ≠ w := by
      intro h
      subst w
      exact hR.loopless v hvw
    rcases lt_or_gt_of_ne hvwne with hlt | hgt
    · have hnot : ¬ R w v := (hR.orient v w hvwne).1 hvw
      exact ⟨(v,w), (mem_edges v w).2 hlt, by simp [orientEdge, hnot]⟩
    · exact ⟨(w,v), (mem_edges w v).2 hgt, by simp [orientEdge, hvw]⟩
end
