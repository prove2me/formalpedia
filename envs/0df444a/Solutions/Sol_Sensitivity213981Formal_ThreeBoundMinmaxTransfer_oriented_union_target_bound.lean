-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_target_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:23:10.487228+00:00
-- url     : https://prove2.me/submissions/99dce102-b243-4e5e-8297-5497cfdcb1b4

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_target_repair_subset
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_union_weighted


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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
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
/- Exact unions of destruction and repair bits for oriented min/max rows. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped BigOperators Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]







theorem oriented_union_target_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tl gi gl : L) (degree b a u : ℕ)
    (hb : BBound F ui tl b) (ha : ABound F gl gi a)
    (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hd : (outgoing S v).card=degree)
    (hvi : orientedRow S F ti ui gi 0 x v (!c₀))
    (hfalse : F tl (child x v c₀)=false)
    (hother : ∀ c : Bool, c ≠ c₀ → F tl (child x v c)=true)
    (hgl : guardFailures S F gl x v=∅)
    (hu : (flipsTo (F ti) false (child x v c₀) ∪ flipsTo (F tl) true (child x v c₀)).card ≤  u) :
    (flipsTo (orientedRowBool S F ti ui gi 0 v (!c₀)) false x ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤  b+degree*a+u := by
  let Ulo := liftBits v c₀ (flipsTo (F ti) false (child x v c₀) ∪ flipsTo (F tl) true (child x v c₀))
  let Uhi := liftBits v (!c₀) (flipsTo (F ui) false (child x v (!c₀)))
  let W := fun w : V => liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)))
  have hwc : ∀ w ∈ outgoing S v, (W w).card ≤  a := by
    intro w hw
    have hz : F gl (child x w (S.label v w))=false := by
      cases h : F gl (child x w (S.label v w)) with
      | false => rfl
      | true =>
        have hm := (mem_guardFailures S F gl x v w).2 ⟨(Finset.mem_filter.mp hw).2,h⟩
        rw [hgl] at hm
        exact False.elim (Finset.notMem_empty _ hm)
    exact (card_liftBits _ _ _).le.trans (ha _ hz)
  have h := oriented_union_weighted S F hF ti ui gi x v (!c₀) hvi Ulo Uhi W
    (flipsTo (ordinaryRowBool S F tl gl 0 v) true x)
    (by simp only [Bool.not_not]; dsimp [Ulo]; rw [liftBits_union]; exact Finset.subset_union_left)
    (Finset.Subset.refl _)
    (by intro w _; exact Finset.Subset.refl _)
    (by
      intro p hp
      have hh := strict_target_repair_subset S F tl gl x v c₀ hfalse hother hgl hp
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      dsimp [Ulo]
      rw [liftBits_union]
      exact Finset.mem_union_right _ hh)
    u b (fun _ => a)
    (by simpa only [Ulo,card_liftBits] using hu)
    ((card_liftBits _ _ _).le.trans (hb _ (hother (!c₀) (by cases c₀ <;> decide)))) hwc
  simpa [Finset.sum_const,nsmul_eq_mul,hd,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h



end
end ThreeBoundMinmaxTransfer





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
  (ti ui tl gi gl : L) (degree b a u : Nat)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ui tl b)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gl gi a)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (c₀ : Bool)
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hvi :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F ti ui gi
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v (Bool.not c₀))
  (hfalse : @Eq.{1} Bool (F tl (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c₀)) Bool.false)
  (hother :
    ∀ (c : Bool),
      @Ne.{1} Bool c c₀ → @Eq.{1} Bool (F tl (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hgl :
    @Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gl x v)
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} V) (@Finset.instEmptyCollection.{0} V)))
  (hu :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} I
        (@Union.union.{0} (Finset.{0} I)
          (@Finset.instUnion.{0} I fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F ti) Bool.false
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c₀))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F tl) Bool.true
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c₀))))
      u),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
          @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
            (fun (a b : Prod.{0, 0} V Bool) =>
              @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                instDecidableEqBool a b)
            (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRowBool L I V inst_2 S F ti ui gi
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v (Bool.not c₀))
          Bool.false x)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_2 S F tl gl
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
          Bool.true x)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) degree a))
      u) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_target_bound
