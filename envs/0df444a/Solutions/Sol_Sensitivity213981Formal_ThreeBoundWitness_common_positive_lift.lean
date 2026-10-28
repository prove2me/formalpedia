-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundWitness.common_positive_lift
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:35:49.341377+00:00
-- url     : https://prove2.me/submissions/3065ab78-3ea0-4bc3-aa01-abb2cafb184a

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith


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









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]

theorem parent_false_of_targets_false [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool)
    (h : ∀ v : V,
      S.target l (failed S F l x v).card (child x v false) (child x v true) = false) :
    parent S F l x = false := by
  classical
  simp only [parent, decide_eq_false_iff_not]
  rintro ⟨v, _, hv⟩
  rw [h v] at hv
  contradiction







@[simp] theorem child_planted_same (z p : I → Bool) (v : V) (c : Bool) :
    child (planted z p v) v c = p := by
  classical
  funext i
  simp [child, planted]

theorem child_planted_other (z p : I → Bool) (v w : V) (c : Bool) (hw : w ≠ v) :
    child (planted z p v) w c = z := by
  classical
  funext i
  simp [child, planted, hw]

theorem planted_failed_empty [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (v : V) (l : L) :
    failed S F l (planted z p v) v = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro w _ hw
  have hwv : w ≠ v := by
    intro he
    subst w
    exact S.loopless v hw.1
  rw [child_planted_other z p v w (S.label v w) hwv, hz] at hw
  exact Bool.noConfusion hw.2

theorem parent_accepts_planted [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (hp : ∀ l, F l p = true)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true) (v : V) (l : L) :
    parent S F l (planted z p v) = true := by
  apply (parent_true_iff S F l _).2
  refine ⟨v, ?_, ?_⟩
  · simp [planted_failed_empty S F z p hz v l]
  · simpa only [planted_failed_empty S F z p hz v l, Finset.card_empty,
      child_planted_same] using haccept l p p hp hp



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

theorem parent_rejects_after_planted_flip [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (i : I) (hi : ∀ l, F l (_root_.OAI.Paper320.flip p {i}) = false)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (v : V) (c : Bool) (l : L) :
    parent S F l (_root_.OAI.Paper320.flip (planted z p v) {((v,c),i)}) = false := by
  classical
  apply parent_false_of_targets_false
  intro w
  by_cases hw : w = v
  · subst w
    cases c
    · apply hreject
      exact Or.inl (by simpa only [child_flip_same, child_planted_same] using hi)
    · apply hreject
      exact Or.inr (by simpa only [child_flip_same, child_planted_same] using hi)
  · apply hreject
    apply Or.inl
    have hpairs : (w,false) ≠ (v,c) := by
      intro he
      exact hw (congrArg Prod.fst he)
    simpa only [child_flip_other _ v w c false i hpairs,
      child_planted_other z p v w false hw] using hz

/-- The positive common witness doubles its indexed sensitive-bit set. -/
theorem common_positive_lift [Fintype V] {A : Type}
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (z p : I → Bool) (hz : ∀ l, F l z = false) (hp : ∀ l, F l p = true)
    (e : A ↪ I) (he : ∀ a l, F l (_root_.OAI.Paper320.flip p {e a}) = false)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (v : V) :
    ∃ (p' : ((V × Bool) × I) → Bool) (e' : (Bool × A) ↪ ((V × Bool) × I)),
      (∀ l, parent S F l p' = true) ∧
      (∀ a l, parent S F l (_root_.OAI.Paper320.flip p' {e' a}) = false) := by
  let e' : (Bool × A) ↪ ((V × Bool) × I) :=
    ⟨fun a => ((v,a.1),e a.2), by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun q => q.1.2) h
      · exact e.injective (congrArg Prod.snd h)⟩
  refine ⟨planted z p v, e', ?_, ?_⟩
  · exact fun l => parent_accepts_planted S F z p hz hp haccept v l
  · intro a l
    exact parent_rejects_after_planted_flip S F z p hz (e a.2)
      (he a.2) hreject v a.1 l





















/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : Fintype.{0} V] {A : Type} (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (F : L → (I → Bool) → Bool) (z p : I → Bool) (hz : ∀ (l : L), @Eq.{1} Bool (F l z) Bool.false)
  (hp : ∀ (l : L), @Eq.{1} Bool (F l p) Bool.true) (e : Function.Embedding.{1, 1} A I)
  (he :
    ∀ (a : A) (l : L),
      @Eq.{1} Bool
        (F l
          (@OAI.Paper320.flip I p
            (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I)
              (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} A I) A (fun (x : A) => I)
                (@Function.instFunLikeEmbedding.{1, 1} A I) e a))))
        Bool.false)
  (haccept :
    ∀ (l : L) (x y : I → Bool),
      (∀ (a : L), @Eq.{1} Bool (F a x) Bool.true) →
        (∀ (a : L), @Eq.{1} Bool (F a y) Bool.true) →
          @Eq.{1} Bool
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.target L I V S l
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x y)
            Bool.true)
  (hreject :
    ∀ (l : L) (d : Nat) (x y : I → Bool),
      Or (∀ (a : L), @Eq.{1} Bool (F a x) Bool.false) (∀ (a : L), @Eq.{1} Bool (F a y) Bool.false) →
        @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.target L I V S l d x y) Bool.false)
  (v : V),
  @Exists.{1} (Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) fun (p' : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) =>
    @Exists.{1} (Function.Embedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      fun (e' : Function.Embedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)) =>
      And (∀ (l : L), @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst S F l p') Bool.true)
        (∀ (a : Prod.{0, 0} Bool A) (l : L),
          @Eq.{1} Bool
            (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst S F l
              (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) p'
                (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                  (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                  (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                  (@DFunLike.coe.{1, 1, 1}
                    (Function.Embedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                    (Prod.{0, 0} Bool A) (fun (x : Prod.{0, 0} Bool A) => Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                    (@Function.instFunLikeEmbedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)) e'
                    a))))
            Bool.false) := @Sensitivity213981Formal.ThreeBoundWitness.common_positive_lift
