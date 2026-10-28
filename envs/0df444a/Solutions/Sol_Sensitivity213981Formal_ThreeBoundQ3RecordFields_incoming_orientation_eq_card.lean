-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundQ3RecordFields.incoming_orientation_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:31.657231+00:00
-- url     : https://prove2.me/submissions/ef48d123-481b-4ba8-9ccb-23b6dd4e1cf6

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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













end ThreeBoundQ2





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact meanings of the 41 fields of the executable q3 record. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundQ3RecordFields
open ThreeBoundQ3 ThreeBoundNumeric
open ThreeBoundQ2 ( directedEdges_nodup mem_directedEdges)
open scoped Classical BigOperators
noncomputable section

































theorem incoming_orientation_eq_card (ts : List Kind)
    (R : Fin ts.length → Fin ts.length → Prop) [DecidableRel R]
    (hR : TournamentHighRows.IsTournament R) (w : Fin ts.length) :
    incoming ts (orientationBits R) w =
      ((Finset.univ : Finset (Fin ts.length)).filter fun v => isGuard (ts.get v) = true ∧ R v w).card := by
  unfold incoming
  rw [← List.countP_eq_length_filter]
  have hp : (fun e : Fin ts.length × Fin ts.length => isGuard (ts.get e.1) && decide (e.2 = w)) =
      (fun e => decide (isGuard (ts.get e.1) = true ∧ e.2 = w)) := by
    funext e
    simp
  rw [hp,← (directedEdges_nodup R).card_eq_countP]
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    obtain ⟨hed,hef⟩ := Finset.mem_filter.mp he
    have hh : isGuard (ts.get e.1) = true ∧ e.2=w := by simpa using hef
    have hr := (mem_directedEdges R hR e.1 e.2).1 (List.mem_toFinset.mp hed)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hh.2 ▸ hr⟩
  · intro a ha b hb hab
    have haf : isGuard (ts.get a.1) = true ∧ a.2=w := by
      simpa using (Finset.mem_filter.mp ha).2
    have hbf : isGuard (ts.get b.1) = true ∧ b.2=w := by
      simpa using (Finset.mem_filter.mp hb).2
    exact Prod.ext hab (haf.2.trans hbf.2.symm)
  · intro v hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨hg,hr⟩
    refine ⟨(v,w),Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      ((mem_directedEdges R hR v w).2 hr),?_⟩,rfl⟩
    simpa using hg



end
end ThreeBoundQ3RecordFields





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (R :
    Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) →
      Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) → Prop)
  [inst :
    @DecidableRel.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) R]
  (hR :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament
      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) R)
  (w : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
  @Eq.{1} Nat
    (Sensitivity213981Formal.ThreeBoundQ3RecordFields.incoming ts
      (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
        (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) R inst)
      w)
    (@Finset.card.{0} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
      (@Finset.filter.{0} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
        (fun (v : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
          And
            (@Eq.{1} Bool
              (Sensitivity213981Formal.ThreeBoundQ3.isGuard
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts v))
              Bool.true)
            (R v w))
        (fun (a : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
          @instDecidableAnd
            (@Eq.{1} Bool
              (Sensitivity213981Formal.ThreeBoundQ3.isGuard
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts a))
              Bool.true)
            (R a w)
            (instDecidableEqBool
              (Sensitivity213981Formal.ThreeBoundQ3.isGuard
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts a))
              Bool.true)
            (inst a w))
        (@Finset.univ.{0} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
          (Fin.fintype (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))))) := @Sensitivity213981Formal.ThreeBoundQ3RecordFields.incoming_orientation_eq_card
