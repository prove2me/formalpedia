-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundQ2.outCount_orientation_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:56:49.601162+00:00
-- url     : https://prove2.me/submissions/fe2c0413-192c-4cd9-9a3a-5a924e59b6e3

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ2_mem_directedEdges


namespace Sensitivity213981Formal
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
    (i,j) ∈ edges n ↔ i <  j := by
  simp [edges]

theorem edges_nodup (n : ℕ) : (edges n).Nodup := by
  unfold edges
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    exact ((List.nodup_finRange n).filter _).map (fun _ _ h => congrArg Prod.snd h)
  · apply (List.nodup_finRange n).imp
    intro a b hab p hp hq
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hq
    exact hab (congrArg Prod.fst (hi.trans hj.symm))





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

theorem orientEdge_injective_on {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a b : Fin n × Fin n) (ha : a ∈ edges n) (hb : b ∈ edges n)
    (he : orientEdge R a = orientEdge R b) : a = b := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  have ha := (mem_edges a₁ a₂).1 ha
  have hb := (mem_edges b₁ b₂).1 hb
  by_cases h₁ : R a₂ a₁ <;> by_cases h₂ : R b₂ b₁ <;>
    simp only [orientEdge, h₁, h₂, ↓reduceIte, Prod.swap, Prod.mk.injEq] at he
  · exact Prod.ext he.2 he.1
  · rcases he with ⟨rfl,rfl⟩
    exact False.elim (lt_asymm ha hb)
  · rcases he with ⟨rfl,rfl⟩
    exact False.elim (lt_asymm ha hb)
  · exact Prod.ext he.1 he.2

theorem directedEdges_nodup {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    (directedEdges (edges n) (orientationBits R)).Nodup := by
  rw [directedEdges_orientation]
  exact (edges_nodup n).map_on (fun a ha b hb he => orientEdge_injective_on R a b ha hb he)



theorem outCount_eq_countP {V : Type} [DecidableEq V]
    (es : List (V × V)) (ds : List Bool) (v : V) :
    outCount es ds v = (directedEdges es ds).countP (fun e => e.1 = v) := by
  induction es generalizing ds with
  | nil => simp [outCount, directedEdges]
  | cons e es ih =>
      cases ds with
      | nil => simp [outCount, directedEdges]
      | cons d ds =>
          cases d
          · change (if e.1 = v then 1 else 0) + outCount es ds v =
              (e :: directedEdges es ds).countP (fun e => e.1 = v)
            rw [ih]
            by_cases h : e.1 = v <;> simp [List.countP_cons, h, Nat.add_comm]
          · change (if e.2 = v then 1 else 0) + outCount es ds v =
              (e.swap :: directedEdges es ds).countP (fun e => e.1 = v)
            rw [ih]
            by_cases h : e.2 = v <;> simp [List.countP_cons, h, Nat.add_comm]

theorem outCount_orientation_eq_card {n : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R] (hR : TournamentHighRows.IsTournament R) (v : Fin n) :
    outCount (edges n) (orientationBits R) v =
      ((Finset.univ : Finset (Fin n)).filter (R v)).card := by
  classical
  rw [outCount_eq_countP, ← (directedEdges_nodup R).card_eq_countP]
  apply Finset.card_bij (fun e _ => e.2)
  · intro e he
    obtain ⟨hed, hef⟩ := Finset.mem_filter.mp he
    have hr := (mem_directedEdges R hR e.1 e.2).1 (List.mem_toFinset.mp hed)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hef] using hr⟩
  · intro a ha b hb hab
    have haf := (Finset.mem_filter.mp ha).2
    have hbf := (Finset.mem_filter.mp hb).2
    exact Prod.ext (haf.trans hbf.symm) hab
  · intro w hw
    have hr := (Finset.mem_filter.mp hw).2
    exact ⟨(v,w), Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr ((mem_directedEdges R hR v w).2 hr), rfl⟩, rfl⟩







end ThreeBoundQ2





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} (R : Fin n → Fin n → Prop) [inst : @DecidableRel.{1, 1} (Fin n) (Fin n) R]
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament (Fin n) R) (v : Fin n),
  @Eq.{1} Nat
    (@Sensitivity213981Formal.ThreeBoundQ2.outCount (Fin n) (instDecidableEqFin n)
      (Sensitivity213981Formal.ThreeBoundQ2.edges n) (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits n R inst) v)
    (@Finset.card.{0} (Fin n) (@Finset.filter.{0} (Fin n) (R v) (inst v) (@Finset.univ.{0} (Fin n) (Fin.fintype n)))) := @Sensitivity213981Formal.ThreeBoundQ2.outCount_orientation_eq_card
