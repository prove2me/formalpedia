-- Prove2me | solution 1 for ThreeBoundRepair.failed_decrease
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:41:53.911712+00:00
-- url     : https://prove2.me/submissions/b5c04f72-6476-4fdf-b662-afa23a6a7343

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}





























theorem child_flip_same (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (i : I) :
    child (flip x {((v,c),i)}) v c = flip (child x v c) {i} := by
  classical
  funext a
  simp [child, OAI.Paper320.flip]

theorem child_flip_other (x : ((V × Bool) × I) → Bool)
    (v w : V) (c e : Bool) (i : I) (h : (w,e) ≠ (v,c)) :
    child (flip x {((v,c),i)}) w e = child x w e := by
  classical
  funext a
  have hh : ((w,e),a) ≠ ((v,c),i) := by
    intro he
    exact h (congrArg Prod.fst he)
  simp [child, OAI.Paper320.flip, hh]

























/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end

section
/-
Actual parent one-bit repairs are covered by the graded target/guard candidates.
This connects the concrete Boolean functions to the finite q2 type analysis.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundRepair
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
noncomputable section

variable {L I V : Type} [Fintype V]

theorem failed_flip_mem_other (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v w z : V) (c : Bool) (a : I)
    (h : (z, S.label v z) ≠ (w,c)) :
    z ∈ failed S F l (flip x {((w,c),a)}) v ↔ z ∈ failed S F l x v := by
  simp only [failed, Finset.mem_filter, Finset.mem_univ, true_and,
    child_flip_other x w z c (S.label v z) a h]



theorem failed_before_subset_insert_after (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    failed S F l x v ⊆ insert w (failed S F l (flip x {((w,c),a)}) v) := by
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · exact Finset.mem_insert.mpr (Or.inr
      ((failed_flip_mem_other S F l x v w z c a
        (fun h => hzw (congrArg Prod.fst h))).2 hz))





variable [Preorder L]





end
end ThreeBoundRepair





end

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
namespace ThreeBoundRepair
end ThreeBoundRepair
open ThreeBoundRepair
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
variable {L I V : Type} [Fintype V]

/-- A strict decrease of the actual guard count removes exactly the changed
    selected guard, and decreases the count by exactly one. -/
theorem solution (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (hdec : (failed S F l (flip x {((w,c),a)}) v).card < (failed S F l x v).card) :
    S.Adj v w ∧ S.label v w = c ∧
      F (S.guard l) (child x w c) = true ∧
      F (S.guard l) (flip (child x w c) {a}) = false ∧
      (failed S F l x v).card = (failed S F l (flip x {((w,c),a)}) v).card+1 := by
  have hsubset := failed_before_subset_insert_after S F l x v w c a
  have hcard : (failed S F l x v).card ≤ (failed S F l (flip x {((w,c),a)}) v).card+1 :=
    (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _)
  have hwold : w ∈ failed S F l x v := by
    by_contra hn
    have hsub : failed S F l x v ⊆ failed S F l (flip x {((w,c),a)}) v := by
      intro z hz
      rcases Finset.mem_insert.mp (hsubset hz) with hzw | hh
      · exact False.elim (hn (hzw ▸ hz))
      · exact hh
    exact (Nat.not_le_of_lt hdec) (Finset.card_le_card hsub)
  have hwnew : w ∉ failed S F l (flip x {((w,c),a)}) v := by
    intro hn
    have hsub : failed S F l x v ⊆ failed S F l (flip x {((w,c),a)}) v := by
      intro z hz
      rcases Finset.mem_insert.mp (hsubset hz) with hzw | hh
      · exact hzw ▸ hn
      · exact hh
    exact (Nat.not_le_of_lt hdec) (Finset.card_le_card hsub)
  rcases (Finset.mem_filter.mp hwold).2 with ⟨hR,htrue⟩
  have hl : S.label v w = c := by
    by_contra hn
    have hp : (w,S.label v w) ≠ (w,c) := fun h => hn (congrArg Prod.snd h)
    exact hwnew ((failed_flip_mem_other S F l x v w w c a hp).2 hwold)
  have hfalse : F (S.guard l) (flip (child x w c) {a}) = false := by
    cases hh : F (S.guard l) (flip (child x w c) {a}) with
    | false => rfl
    | true =>
        apply False.elim
        apply hwnew
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,hR,by simpa only [hl,child_flip_same] using hh⟩
  exact ⟨hR,hl,by simpa only [hl] using htrue,hfalse,by omega⟩
end
