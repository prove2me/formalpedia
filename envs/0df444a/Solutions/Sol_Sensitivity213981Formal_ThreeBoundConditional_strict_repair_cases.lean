-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.strict_repair_cases
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:39:11.101311+00:00
-- url     : https://prove2.me/submissions/8fe11633-086e-41a8-823e-14f89f538f14

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
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













@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]





























































end
end ThreeBoundConditional




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Strict conditional union transfer for actual Boolean rows and parents. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]







theorem guardFailures_own_flip (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (a : I) :
    guardFailures S F g (_root_.OAI.Paper320.flip x {((v,c),a)}) v = guardFailures S F g x v := by
  ext w
  by_cases hR : S.Adj v w
  · have hw : w ≠ v := by intro he; subst w; exact S.loopless v hR
    simp only [mem_guardFailures,hR,true_and,
      child_flip_other x v w c (S.label v w) a (fun h => hw (congrArg Prod.fst h))]
  · simp only [mem_guardFailures,hR,false_and]

/-- A strict row can be repaired only at its unique failed target or guard. -/
theorem strict_repair_cases (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (hoff : ¬ordinaryRow S F t g 0 x v)
    (hon : ordinaryRow S F t g 0 (_root_.OAI.Paper320.flip x {((w,c),a)}) v) :
    (w=v ∧ F t (child x v c)=false ∧
      (∀ e : Bool, e ≠ c → F t (child x v e)=true) ∧
      guardFailures S F g x v = ∅ ∧ F t (_root_.OAI.Paper320.flip (child x v c) {a})=true) ∨
    ((∀ e : Bool, F t (child x v e)=true) ∧ guardFailures S F g x v = {w} ∧
      S.Adj v w ∧ S.label v w=c ∧ F g (child x w c)=true ∧
      F g (_root_.OAI.Paper320.flip (child x w c) {a})=false) := by
  have hfempty : guardFailures S F g (_root_.OAI.Paper320.flip x {((w,c),a)}) v = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hon.2)
  by_cases hw : w=v
  · subst w
    have hg : guardFailures S F g x v = ∅ := by
      rw [guardFailures_own_flip] at hfempty
      exact hfempty
    have hother : ∀ e : Bool, e ≠ c → F t (child x v e)=true := by
      intro e he
      have h := hon.1 e
      rw [child_flip_other x v v c e a (fun h => he (congrArg Prod.snd h))] at h
      exact h
    have hfalse : F t (child x v c)=false := by
      cases h : F t (child x v c) with
      | false => rfl
      | true =>
        apply False.elim
        apply hoff
        refine ⟨?_,by simp [hg]⟩
        intro e
        by_cases he : e=c
        · simpa only [he] using h
        · exact hother e he
    exact Or.inl ⟨rfl,hfalse,hother,hg,by simpa only [child_flip_same] using hon.1 c⟩
  · have ht : ∀ e : Bool, F t (child x v e)=true := by
      intro e
      have h := hon.1 e
      rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)] at h
      exact h
    have hex : (guardFailures S F g x v).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hoff ⟨ht,by simp [he]⟩
    obtain ⟨z,hz⟩ := hex
    have hzprop := (mem_guardFailures S F g x v z).1 hz
    have hloc : (z,S.label v z)=(w,c) := by
      by_contra hp
      have hf : F g (child (_root_.OAI.Paper320.flip x {((w,c),a)}) z (S.label v z))=true := by
        rw [child_flip_other x w z c (S.label v z) a hp]
        exact hzprop.2
      have hmem := (mem_guardFailures S F g _ v z).2 ⟨hzprop.1,hf⟩
      rw [hfempty] at hmem
      exact Finset.notMem_empty _ hmem
    have he : z=w := congrArg Prod.fst hloc
    subst z
    have hl : S.label v w=c := congrArg Prod.snd hloc
    have hsingleton : guardFailures S F g x v = {w} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hz,?_⟩
      intro z hz
      by_contra hzw
      obtain ⟨hR,hf⟩ := (mem_guardFailures S F g x v z).1 hz
      have hf' : F g (child (_root_.OAI.Paper320.flip x {((w,c),a)}) z (S.label v z))=true := by
        rw [child_flip_other x w z c (S.label v z) a (fun h => hzw (congrArg Prod.fst h))]
        exact hf
      have hmem := (mem_guardFailures S F g _ v z).2 ⟨hR,hf'⟩
      rw [hfempty] at hmem
      exact Finset.notMem_empty _ hmem
    have hafter : F g (_root_.OAI.Paper320.flip (child x w c) {a})=false := by
      cases h : F g (_root_.OAI.Paper320.flip (child x w c) {a}) with
      | false => rfl
      | true =>
        have hmem : w ∈ guardFailures S F g (_root_.OAI.Paper320.flip x {((w,c),a)}) v := by
          apply (mem_guardFailures S F g _ v w).2
          refine ⟨hzprop.1,?_⟩
          rw [hl,child_flip_same]
          exact h
        rw [hfempty] at hmem
        exact False.elim (Finset.notMem_empty _ hmem)
    exact Or.inr ⟨ht,hsingleton,hzprop.1,hl,by simpa only [hl] using hzprop.2,hafter⟩



























end
end ThreeBoundConditional



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [LinearOrder.{0} L] [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (t g : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (c : Bool) (a : I)
  (hoff :
    Not
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst S F t g
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v))
  (hon :
    @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst S F t g
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
        (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
      v),
  Or
    (And (@Eq.{1} V w v)
      (And (@Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.false)
        (And
          (∀ (e : Bool),
            @Ne.{1} Bool e c →
              @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v e)) Bool.true)
          (And
            (@Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst S F g x v)
              (@EmptyCollection.emptyCollection.{0} (Finset.{0} V) (@Finset.instEmptyCollection.{0} V)))
            (@Eq.{1} Bool
              (F t
                (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)
                  (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
              Bool.true)))))
    (And (∀ (e : Bool), @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v e)) Bool.true)
      (And
        (@Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst S F g x v)
          (@Singleton.singleton.{0, 0} V (Finset.{0} V) (@Finset.instSingleton.{0} V) w))
        (And (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w)
          (And (@Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w) c)
            (And (@Eq.{1} Bool (F g (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)) Bool.true)
              (@Eq.{1} Bool
                (F g
                  (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)
                    (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
                Bool.false)))))) := @Sensitivity213981Formal.ThreeBoundConditional.strict_repair_cases
