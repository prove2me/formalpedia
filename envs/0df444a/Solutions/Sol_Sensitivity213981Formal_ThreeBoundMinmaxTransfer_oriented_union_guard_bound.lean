-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_guard_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:23:11.023001+00:00
-- url     : https://prove2.me/submissions/425f0e3d-1436-4a1f-8f60-d60df138ba31

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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_guard_repair_subset
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



theorem finset_sum_special {J : Type} [DecidableEq J] (A : Finset J) (w₀ : J)
    (hw : w₀ ∈ A) (p a : ℕ) :
    (∑ w ∈ A, if w=w₀ then p else a)=(A.card-1)*a+p := by
  calc
    _ = (∑ w ∈ A.erase w₀, if w=w₀ then p else a)+p := by
      simpa using (Finset.sum_erase_add A (fun w => if w=w₀ then p else a) hw).symm
    _ = (A.card-1)*a+p := by
      have he : (∑ w ∈ A.erase w₀, if w=w₀ then p else a)=∑ _w ∈ A.erase w₀, a := by
        apply Finset.sum_congr rfl
        intro w hw
        exact if_neg (Finset.ne_of_mem_erase hw)
      rw [he]
      simp [Finset.card_erase_of_mem hw]








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









theorem oriented_union_guard_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tl gi gl : L) (degree b0 b1 a u : ℕ)
    (hb0 : BBound F ti tl b0) (hb1 : BBound F ui tl b1) (ha : ABound F gl gi a)
    (x : ((V × Bool) × I) → Bool) (v w₀ : V) (c : Bool)
    (hd : (outgoing S v).card=degree)
    (hvi : orientedRow S F ti ui gi 0 x v c)
    (ht : ∀ e : Bool, F tl (child x v e)=true)
    (hgl : guardFailures S F gl x v={w₀})
    (hu : (flipsTo (F gi) true (child x w₀ (S.label v w₀)) ∪
      flipsTo (F gl) false (child x w₀ (S.label v w₀))).card ≤  u) :
    (flipsTo (orientedRowBool S F ti ui gi 0 v c) false x ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card ≤  b0+b1+(degree-1)*a+u := by
  let Ulo := liftBits v (!c) (flipsTo (F ti) false (child x v (!c)))
  let Uhi := liftBits v c (flipsTo (F ui) false (child x v c))
  let W := fun w : V => liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)) ∪
    if w=w₀ then flipsTo (F gl) false (child x w (S.label v w)) else ∅)
  have hwmem : w₀ ∈ guardFailures S F gl x v := by rw [hgl]; simp
  have hwout : w₀ ∈ outgoing S v := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,((mem_guardFailures S F gl x v w₀).1 hwmem).1⟩
  have hwc : ∀ w ∈ outgoing S v, (W w).card ≤  if w=w₀ then u else a := by
    intro w hw
    by_cases he : w=w₀
    · subst w; simpa [W] using hu
    · have hz : F gl (child x w (S.label v w))=false := by
        cases h : F gl (child x w (S.label v w)) with
        | false => rfl
        | true =>
          have hm := (mem_guardFailures S F gl x v w).2 ⟨(Finset.mem_filter.mp hw).2,h⟩
          rw [hgl,Finset.mem_singleton] at hm
          exact False.elim (he hm)
      simpa only [W,if_neg he,Finset.union_empty,card_liftBits] using ha _ hz
  have h := oriented_union_weighted S F hF ti ui gi x v c hvi Ulo Uhi W
    (flipsTo (ordinaryRowBool S F tl gl 0 v) true x)
    (Finset.Subset.refl _) (Finset.Subset.refl _)
    (by intro w _; dsimp [W]; rw [liftBits_union]; exact Finset.subset_union_left)
    (by
      intro p hp
      have hh := strict_guard_repair_subset S F tl gl x v w₀ ht hgl hp
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨w₀,hwout,?_⟩
      dsimp [W]
      rw [if_pos rfl,liftBits_union]
      exact Finset.mem_union_right _ hh)
    b0 b1 (fun w => if w=w₀ then u else a)
    ((card_liftBits _ _ _).le.trans (hb0 _ (ht (!c))))
    ((card_liftBits _ _ _).le.trans (hb1 _ (ht c))) hwc
  rw [finset_sum_special _ _ hwout,hd] at h
  omega

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
  (ti ui tl gi gl : L) (degree b0 b1 a u : Nat)
  (hb0 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tl b0)
  (hb1 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ui tl b1)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gl gi a)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w₀ : V) (c : Bool)
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hvi :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F ti ui gi
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c)
  (ht : ∀ (e : Bool), @Eq.{1} Bool (F tl (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v e)) Bool.true)
  (hgl :
    @Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gl x v)
      (@Singleton.singleton.{0, 0} V (Finset.{0} V) (@Finset.instSingleton.{0} V) w₀))
  (hu :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} I
        (@Union.union.{0} (Finset.{0} I)
          (@Finset.instUnion.{0} I fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F gi) Bool.true
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
              (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F gl) Bool.false
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
              (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))))
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
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v c)
          Bool.false x)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_2 S F tl gl
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
          Bool.true x)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b0 b1)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          a))
      u) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_guard_bound
