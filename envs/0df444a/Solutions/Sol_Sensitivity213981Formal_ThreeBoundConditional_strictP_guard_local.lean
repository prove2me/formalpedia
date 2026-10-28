-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.strictP_guard_local
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:56:53.756991+00:00
-- url     : https://prove2.me/submissions/4a6c16c9-6f08-4694-984b-17ddf5d99aa6

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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_same_row_up_guard_subset
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













theorem targetBits_card_le (F : L → (I → Bool) → Bool) (ti tj : L)
    (x : ((V × Bool) × I) → Bool) (v : V) (b : ℕ)
    (hb : BBound F ti tj b) (hstrong : ∀ c : Bool, F tj (child x v c) = true) :
    (targetBits F ti x v).card ≤  2*b := by
  calc
    (targetBits F ti x v).card ≤ 
        (flipsTo (F ti) false (child x v false)).card +
        (flipsTo (F ti) false (child x v true)).card := by
      simpa only [targetBits, card_liftBits] using Finset.card_union_le
        (liftBits v false (flipsTo (F ti) false (child x v false)))
        (liftBits v true (flipsTo (F ti) false (child x v true)))
    _ ≤  b+b := Nat.add_le_add (hb _ (hstrong false)) (hb _ (hstrong true))
    _ = 2*b := by omega











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













@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]










































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

theorem zero_row_guard_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V)
    (hv : ordinaryRow S F t g 0 x v) (w : V) (hvw : S.Adj v w) :
    F g (child x w (S.label v w)) = false := by
  have hempty : guardFailures S F g x v = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hv.2)
  cases hf : F g (child x w (S.label v w)) with
  | false => rfl
  | true =>
    have hm := (mem_guardFailures S F g x v w).2 ⟨hvw,hf⟩
    rw [hempty] at hm
    exact False.elim (Finset.notMem_empty _ hm)



































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

































/-- Guard-defect cross repairs use stronger target states if a same-row repair exists. -/
theorem strictP_guard_local (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (tj tk tl gj gk gl : L) (hg : gl ≤  gk)
    (x : ((V × Bool) × I) → Bool) (v : V)
    (hvj : ordinaryRow S F tj gj 0 x v)
    (htk : ∀ c : Bool, F tk (child x v c)=true)
    (hvk : ¬ordinaryRow S F tk gk 0 x v)
    (bₖ bₗ m : ℕ) (hbₖ : BBound F gl tk bₖ) (hbₗ : BBound F gl tl bₗ)
    (hm : MBound F gl gk gj m) :
    (targetBits F gl x v ∪ flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤ 
      max (2*bₖ) (2*bₗ+m) := by
  by_cases he : flipsTo (ordinaryRowBool S F tl gl 0 v) true x=∅
  · rw [he,Finset.union_empty]
    exact (targetBits_card_le F gl tk x v bₖ hbₖ htk).trans (le_max_left _ _)
  · have hnon : (guardFailures S F gk x v).Nonempty := by
      by_contra hn
      have hh := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hvk ⟨htk,by simp [hh]⟩
    obtain ⟨w₀,hw₀⟩ := hnon
    obtain ⟨hR,hk⟩ := (mem_guardFailures S F gk x v w₀).1 hw₀
    have hj := zero_row_guard_false S F tj gj x v hvj w₀ hR
    have hsub := same_row_up_guard_subset S F hF gk tl gl hg x v w₀ hR hk
    have hup : (flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤  m := by
      have hh := Finset.card_le_card hsub
      rw [card_liftBits] at hh
      exact hh.trans (hm _ hk hj)
    obtain ⟨⟨⟨w,c⟩,a⟩,ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨hw,hc,_⟩ := (mem_liftBits _ _ _ _ _ _).1 (hsub ha)
    subst w
    have hon := (ordinary_row_true S F tl gl 0 _ v).1 (Finset.mem_filter.mp ha).2
    have hne : v ≠ w₀ := by intro h; subst w₀; exact S.loopless v hR
    have htl : ∀ e : Bool, F tl (child x v e)=true := by
      intro e
      have h := hon.1 e
      rw [child_flip_other x w₀ v c e a (fun h => hne (congrArg Prod.fst h))] at h
      exact h
    exact ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (targetBits_card_le F gl tl x v bₗ hbₗ htl) hup)).trans (le_max_right _ _)



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
  (tj tk tl gj gk gl : L)
  (hg :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl gk)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V)
  (hvj :
    @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tj gj
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v)
  (htk : ∀ (c : Bool), @Eq.{1} Bool (F tk (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hvk :
    Not
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tk gk
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v))
  (bₖ bₗ m : Nat) (hbₖ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tk bₖ)
  (hbₗ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tl bₗ)
  (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl gk gj m),
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
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) bₖ)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) bₗ)
        m)) := @Sensitivity213981Formal.ThreeBoundConditional.strictP_guard_local
