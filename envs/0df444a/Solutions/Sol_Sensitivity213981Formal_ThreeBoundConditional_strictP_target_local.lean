-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.strictP_target_local
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:40:16.150004+00:00
-- url     : https://prove2.me/submissions/2abb20a9-d517-42f7-a6e1-264e6e0b4ad6

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
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
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_targetBits_conditional_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_mem_liftBits


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
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _

























end
end ThreeBoundPositive






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
























































@[simp] theorem ordinary_row_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    ordinaryRowBool S F t g q v x = true ↔ ordinaryRow S F t g q x v := by
  simp [ordinaryRowBool]


















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
























theorem liftBits_union (v : V) (c : Bool) (A B : Finset I) :
    liftBits v c (A ∪ B) = liftBits v c A ∪ liftBits v c B := by
  exact Finset.map_union _ _












end
end ThreeBoundConditional



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Refined strict conditional positive transfer, including source-labeled cap. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]


















/-- A known missing intermediate target pins every same-row strong repair. -/
theorem same_row_up_target_location (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tk tl gl : L) (ht : tk ≤  tl)
    (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hmiss : F tk (child x v c₀)=false) (w : V) (c : Bool) (a : I)
    (hon : ordinaryRow S F tl gl 0 (_root_.OAI.Paper320.flip x {((w,c),a)}) v) :
    (v,c₀)=(w,c) := by
  by_contra hn
  have hh := hon.1 c₀
  rw [child_flip_other x w v c c₀ a hn] at hh
  have hk := hF _ _ ht _ hh
  rw [hmiss] at hk
  contradiction

theorem same_row_up_target_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tk tl gl : L) (ht : tk ≤  tl)
    (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hmiss : F tk (child x v c₀)=false) :
    flipsTo (ordinaryRowBool S F tl gl 0 v) true x ⊆
      liftBits v c₀ (flipsTo (F tl) true (child x v c₀)) := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F tl gl 0 _ v).1 (Finset.mem_filter.mp ha).2
  have hh := same_row_up_target_location S F hF tk tl gl ht x v c₀ hmiss w c a hon
  cases hh
  apply (mem_liftBits _ _ _ _ _ _).2
  exact ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [child_flip_same] using hon.1 c₀⟩⟩







/-- Two private-child boundaries plus repair of one child can use a joint bound. -/
theorem targetBits_union_one_up_card (F : L → (I → Bool) → Bool)
    (gi tl : L) (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (E : Finset ((V × Bool) × I))
    (he : E ⊆ liftBits v c₀ (flipsTo (F tl) true (child x v c₀))) (u b : ℕ)
    (hu : (flipsTo (F gi) false (child x v c₀) ∪ flipsTo (F tl) true (child x v c₀)).card ≤  u)
    (hb : ∀ c : Bool, c ≠ c₀ → (flipsTo (F gi) false (child x v c)).card ≤  b) :
    (targetBits F gi x v ∪ E).card ≤  u+b := by
  have hh := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl (targetBits F gi x v)) he)
  apply hh.trans
  cases c₀
  · rw [targetBits,Finset.union_right_comm,← liftBits_union]
    exact (Finset.card_union_le _ _).trans (by simpa only [card_liftBits] using Nat.add_le_add hu (hb true (by decide)))
  · rw [targetBits,Finset.union_assoc,← liftBits_union]
    exact (Finset.card_union_le _ _).trans (by
      have hh := Nat.add_le_add (hb false (by decide)) hu
      simpa only [card_liftBits,Nat.add_comm] using hh)


/-- Target-defect cross repairs and same-row repairs share their private child. -/
theorem strictP_target_local (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tj tk tl gl : L) (ht : tk ≤  tl)
    (x : ((V × Bool) × I) → Bool) (v : V)
    (htj : ∀ c : Bool, F tj (child x v c)=true)
    (hmiss : ∃ c : Bool, F tk (child x v c)=false)
    (m bₖ bₗ u : ℕ) (hm : MBound F gl tj tk m)
    (hbₖ : BBound F gl tk bₖ) (hbₗ : BBound F gl tl bₗ) (hu : DBound F gl tj tk tl u) :
    (targetBits F gl x v ∪ flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ 
      max (max (2*m) (m+bₖ)) (u+bₗ) := by
  by_cases he : flipsTo (ordinaryRowBool S F tl gl 0 v) true x=∅
  · rw [he,Finset.union_empty]
    exact (targetBits_conditional_card F gl tj tk x v m bₖ hm hbₖ htj hmiss).trans (le_max_left _ _)
  · obtain ⟨⟨⟨w,c⟩,a⟩,ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨c₀,hc₀⟩ := hmiss
    have hon := (ordinary_row_true S F tl gl 0 _ v).1 (Finset.mem_filter.mp ha).2
    have hloc := same_row_up_target_location S F hF tk tl gl ht x v c₀ hc₀ w c a hon
    have hw : v=w := congrArg Prod.fst hloc
    subst w
    have hc : c₀=c := congrArg Prod.snd hloc
    subst c
    have hother : ∀ e : Bool, e ≠ c₀ → F tl (child x v e)=true := by
      intro e he
      have h := hon.1 e
      rw [child_flip_other x v v c₀ e a (fun h => he (congrArg Prod.snd h))] at h
      exact h
    have hbound := targetBits_union_one_up_card F gl tl x v c₀ _
      (same_row_up_target_subset S F hF tk tl gl ht x v c₀ hc₀) u bₗ
      (hu _ (htj c₀) hc₀) (fun e he => hbₗ _ (hother e he))
    exact hbound.trans (le_max_right _ _)





end
end ThreeBoundConditional




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (tj tk tl gl : L)
  (ht :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tk tl)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V)
  (htj : ∀ (c : Bool), @Eq.{1} Bool (F tj (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hmiss :
    @Exists.{1} Bool fun (c : Bool) =>
      @Eq.{1} Bool (F tk (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.false)
  (m bₖ bₗ u : Nat) (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl tj tk m)
  (hbₖ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tk bₖ)
  (hbₗ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tl bₗ)
  (hu : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F gl tj tk tl u),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
          @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
            (fun (a b : Prod.{0, 0} V Bool) =>
              @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                instDecidableEqBool a b)
            (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
        (@Sensitivity213981Formal.ThreeBoundPositive.targetBits L I V inst_1 F gl x v)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_2 S F tl gl
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
          Bool.true x)))
    (@Max.max.{0} Nat Nat.instMax
      (@Max.max.{0} Nat Nat.instMax
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m bₖ))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u bₗ)) := @Sensitivity213981Formal.ThreeBoundConditional.strictP_target_local
