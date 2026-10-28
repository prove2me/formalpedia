-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRepair.failed_decrease
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:26:43.44298+00:00
-- url     : https://prove2.me/submissions/1d0dacfd-6402-4d06-8c67-7ef6b7fd3633

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum


namespace Sensitivity213981Formal
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
    child (_root_.OAI.Paper320.flip x {((v,c),i)}) v c = _root_.OAI.Paper320.flip (child x v c) {i} := by
  classical
  funext a
  simp [child, _root_.OAI.Paper320.flip]

theorem child_flip_other (x : ((V × Bool) × I) → Bool)
    (v w : V) (c e : Bool) (i : I) (h : (w,e) ≠ (v,c)) :
    child (_root_.OAI.Paper320.flip x {((v,c),i)}) w e = child x w e := by
  classical
  funext a
  have hh : ((w,e),a) ≠ ((v,c),i) := by
    intro he
    exact h (congrArg Prod.fst he)
  simp [child, _root_.OAI.Paper320.flip, hh]

























/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
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
    z ∈ failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v ↔ z ∈ failed S F l x v := by
  simp only [failed, Finset.mem_filter, Finset.mem_univ, true_and,
    child_flip_other x w z c (S.label v z) a h]



theorem failed_before_subset_insert_after (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    failed S F l x v ⊆ insert w (failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v) := by
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · exact Finset.mem_insert.mpr (Or.inr
      ((failed_flip_mem_other S F l x v w z c a
        (fun h => hzw (congrArg Prod.fst h))).2 hz))

/-- A strict decrease of the actual guard count removes exactly the changed
    selected guard, and decreases the count by exactly one. -/
theorem failed_decrease (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (hdec : (failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card <  (failed S F l x v).card) :
    S.Adj v w ∧ S.label v w = c ∧
      F (S.guard l) (child x w c) = true ∧
      F (S.guard l) (_root_.OAI.Paper320.flip (child x w c) {a}) = false ∧
      (failed S F l x v).card = (failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card+1 := by
  have hsubset := failed_before_subset_insert_after S F l x v w c a
  have hcard : (failed S F l x v).card ≤  (failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card+1 :=
    (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _)
  have hwold : w ∈ failed S F l x v := by
    by_contra hn
    have hsub : failed S F l x v ⊆ failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v := by
      intro z hz
      rcases Finset.mem_insert.mp (hsubset hz) with hzw | hh
      · exact False.elim (hn (hzw ▸ hz))
      · exact hh
    exact (Nat.not_le_of_lt hdec) (Finset.card_le_card hsub)
  have hwnew : w ∉ failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v := by
    intro hn
    have hsub : failed S F l x v ⊆ failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v := by
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
  have hfalse : F (S.guard l) (_root_.OAI.Paper320.flip (child x w c) {a}) = false := by
    cases hh : F (S.guard l) (_root_.OAI.Paper320.flip (child x w c) {a}) with
    | false => rfl
    | true =>
        apply False.elim
        apply hwnew
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,hR,by simpa only [hl,child_flip_same] using hh⟩
  exact ⟨hR,hl,by simpa only [hl] using htrue,hfalse,by omega⟩



variable [Preorder L]





end
end ThreeBoundRepair





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : Fintype.{0} V] (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (F : L → (I → Bool) → Bool) (l : L) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (c : Bool) (a : I)
  (hdec :
    @LT.lt.{0} Nat instLTNat
      (@Finset.card.{0} V
        (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l
          (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
            (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
              (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
              (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
              (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
          v))
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l x v))),
  And (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w)
    (And (@Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w) c)
      (And
        (@Eq.{1} Bool
          (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S l)
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c))
          Bool.true)
        (And
          (@Eq.{1} Bool
            (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S l)
              (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)
                (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
            Bool.false)
          (@Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l x v))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Finset.card.{0} V
                (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l
                  (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
                    (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                      (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                      (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                      (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
                  v))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := @Sensitivity213981Formal.ThreeBoundRepair.failed_decrease
