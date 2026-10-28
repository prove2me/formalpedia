-- Prove2me | solution 1 for ThreeBoundConditional.ordinary_destroying_cover
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:40:47.907401+00:00
-- url     : https://prove2.me/submissions/50b02fcc-a0bb-473b-b7d3-9f9be6905b07

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
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









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤ S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]



















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
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









@[simp] theorem ordinary_failed (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g l : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (ordinaryStage S F t g q) F l x v = guardFailures S F g x v := rfl

@[simp] theorem ordinary_parent_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent_true_iff, ordinary_failed, ordinaryStage,
    Bool.and_eq_true, ordinaryRow]
  constructor
  · rintro ⟨v,hc,hf,ht⟩
    exact ⟨v, fun c => by cases c <;> assumption, hc⟩
  · rintro ⟨v,ht,hc⟩
    exact ⟨v,hc,ht false,ht true⟩

@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]





























































end
end ThreeBoundConditional




end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem solution (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (w : V) (c : Bool) (a : I)
    (hoff : ordinaryParent S F ti gi qi (flip x {((w,c),a)}) = false) :
    (w = v ∧ F ti (flip (child x v c) {a}) = false) ∨
      (S.Adj v w ∧ S.label v w = c ∧ F gj (child x w c) = false ∧
        F gi (flip (child x w c) {a}) = true) := by
  by_cases he : S.Adj v w ∧ S.label v w = c ∧ F gj (child x w c) = false ∧
        F gi (flip (child x w c) {a}) = true
  · exact Or.inr he
  · have hsub : guardFailures S F gi (flip x {((w,c),a)}) v ⊆ guardFailures S F gj x v := by
      intro z hz
      obtain ⟨hR,hf⟩ := (mem_guardFailures S F gi _ v z).1 hz
      apply (mem_guardFailures S F gj x v z).2
      refine ⟨hR,?_⟩
      by_cases hp : (z,S.label v z) = (w,c)
      · have hzw : z = w := congrArg Prod.fst hp
        have hl : S.label v z = c := congrArg Prod.snd hp
        subst z
        rw [hl,child_flip_same] at hf
        cases hb : F gj (child x w c) with
        | true => simpa only [hl] using hb
        | false => exact False.elim (he ⟨hR,hl,hb,hf⟩)
      · rw [child_flip_other x w z c (S.label v z) a hp] at hf
        exact hF _ _ hg _ hf
    have hc : (guardFailures S F gi (flip x {((w,c),a)}) v).card ≤ qi :=
      (Finset.card_le_card hsub).trans (hv.2.trans hq)
    left
    by_cases hw : w = v
    · subst w
      refine ⟨rfl,?_⟩
      cases hf : F ti (flip (child x v c) {a}) with
      | false => rfl
      | true =>
        have hon : ordinaryParent S F ti gi qi (flip x {((v,c),a)}) = true := by
          apply (ordinary_parent_true S F ti gi qi _).2
          refine ⟨v,?_,hc⟩
          intro e
          by_cases hec : e = c
          · subst e; simpa only [child_flip_same] using hf
          · rw [child_flip_other x v v c e a (fun h => hec (congrArg Prod.snd h))]
            exact hF _ _ ht _ (hv.1 e)
        rw [hoff] at hon
        contradiction
    · have hon : ordinaryParent S F ti gi qi (flip x {((w,c),a)}) = true := by
        apply (ordinary_parent_true S F ti gi qi _).2
        refine ⟨v,?_,hc⟩
        intro e
        rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)]
        exact hF _ _ ht _ (hv.1 e)
      rw [hoff] at hon
      contradiction
end
