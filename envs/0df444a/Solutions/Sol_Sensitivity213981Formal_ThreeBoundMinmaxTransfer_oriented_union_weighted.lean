-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_weighted
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:15:28.460017+00:00
-- url     : https://prove2.me/submissions/0e877e88-743a-4411-9e20-25f6da63dcc2

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_down_cover


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




























@[simp] theorem mem_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passingGuards S F g x v ↔
      S.Adj v w ∧ F g (child x w (S.label v w)) = false := by
  simp only [passingGuards, outgoing, guardFailures, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases F g (child x w (S.label v w)) <;> simp














































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
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped BigOperators Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]





theorem oriented_union_weighted (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui gi : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (hv : orientedRow S F ti ui gi 0 x v c)
    (Ulo Uhi : Finset ((V × Bool) × I)) (W : V → Finset ((V × Bool) × I))
    (E : Finset ((V × Bool) × I))
    (hlo : liftBits v (!c) (flipsTo (F ti) false (child x v (!c))) ⊆ Ulo)
    (hhi : liftBits v c (flipsTo (F ui) false (child x v c)) ⊆ Uhi)
    (hg : ∀ w ∈ outgoing S v,
      liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w))) ⊆ W w)
    (he : E ⊆ Ulo ∪ Uhi ∪ (outgoing S v).biUnion W)
    (ulo uhi : ℕ) (z : V → ℕ) (hUlo : Ulo.card ≤  ulo) (hUhi : Uhi.card ≤  uhi)
    (hW : ∀ w ∈ outgoing S v, (W w).card ≤  z w) :
    (flipsTo (orientedRowBool S F ti ui gi 0 v c) false x ∪ E).card ≤ 
      ulo+uhi+∑ w ∈ outgoing S v, z w := by
  have hsub : flipsTo (orientedRowBool S F ti ui gi 0 v c) false x ∪ E ⊆
      Ulo ∪ Uhi ∪ (outgoing S v).biUnion W := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have hh := oriented_down_cover S F hF ti ui ti ui gi gi le_rfl le_rfl le_rfl 0 x v c hv hp
      rcases Finset.mem_union.mp hh with ht | hguard
      · apply Finset.mem_union_left
        rcases Finset.mem_union.mp ht with ht | ht
        · exact Finset.mem_union_left _ (hlo ht)
        · exact Finset.mem_union_right _ (hhi ht)
      · obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp hguard
        have hw' : w ∈ outgoing S v := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,((mem_passingGuards S F gi x v w).1 hw).1⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w,hw',hg w hw' hp⟩)
    · exact he hp
  have hcU : (Ulo ∪ Uhi).card ≤  ulo+uhi :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hUlo hUhi)
  have hcW : ((outgoing S v).biUnion W).card ≤  ∑ w ∈ outgoing S v, z w :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum hW)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hcU hcW))





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
  (ti ui gi : L) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (c : Bool)
  (hv :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F ti ui gi
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c)
  (Ulo Uhi : Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)) (W : V → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
  (E : Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
  (hlo :
    @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
      (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V v (Bool.not c)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F ti) Bool.false
          (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v (Bool.not c))))
      Ulo)
  (hhi :
    @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
      (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V v c
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F ui) Bool.false
          (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)))
      Uhi)
  (hg :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) w →
        @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
              (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
          (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V w
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w)
            (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F gi) Bool.true
              (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w
                (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w))))
          (W w))
  (he :
    @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
      E
      (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
          @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
            (fun (a b : Prod.{0, 0} V Bool) =>
              @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                instDecidableEqBool a b)
            (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
        (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
            @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
              (fun (a b : Prod.{0, 0} V Bool) =>
                @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                  instDecidableEqBool a b)
              (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
          Ulo Uhi)
        (@Finset.biUnion.{0, 0} V (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
            @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
              (fun (a b : Prod.{0, 0} V Bool) =>
                @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                  instDecidableEqBool a b)
              (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
          (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) W)))
  (ulo uhi : Nat) (z : V → Nat)
  (hUlo : @LE.le.{0} Nat instLENat (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) Ulo) ulo)
  (hUhi : @LE.le.{0} Nat instLENat (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) Uhi) uhi)
  (hW :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) w →
        @LE.le.{0} Nat instLENat (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (W w)) (z w)),
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
        E))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ulo uhi)
      (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid
        (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) fun (w : V) => z w)) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_weighted
