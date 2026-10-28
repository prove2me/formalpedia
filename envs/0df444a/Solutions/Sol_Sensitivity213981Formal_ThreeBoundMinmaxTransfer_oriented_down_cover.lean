-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_down_cover
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:08:00.188448+00:00
-- url     : https://prove2.me/submissions/8adec8f0-e85c-4a6b-abff-9266fe1d6de9

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
/- Conditional destruction of the actual oriented min/max witness row.
The selected orientation is a genuine component of the symmetric parent. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]







theorem oriented_row_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u g : L) (q : ℕ) (w : V) (c : Bool) (x : ((V × Bool) × I) → Bool) :
    orientedRowBool S F t u g q w c x=false ↔ ¬orientedRow S F t u g q x w c := by
  simp only [orientedRowBool,decide_eq_false_iff_not]





theorem oriented_down_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tj uj gi gj : L) (ht : ti ≤  tj) (hu : ui ≤  uj) (hg : gj ≤  gi)
    (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hj : orientedRow S F tj uj gj q x v c₀) :
    flipsTo (orientedRowBool S F ti ui gi q v c₀) false x ⊆
      orientedBits F ti ui x v c₀ ∪ ordinaryGuardBits S F gi gj x v := by
  intro bit hbit
  obtain ⟨⟨w,c⟩,a⟩ := bit
  have hoff := (oriented_row_false S F ti ui gi q v c₀ _).1 (Finset.mem_filter.mp hbit).2
  by_cases he : S.Adj v w ∧ S.label v w=c ∧ F gj (child x w c)=false ∧ F gi (_root_.OAI.Paper320.flip (child x w c) {a})=true
  · apply Finset.mem_union_right
    obtain ⟨hR,hl,hbefore,hafter⟩ := he
    apply Finset.mem_biUnion.mpr
    refine ⟨w,(mem_passingGuards S F gj x v w).2 ⟨hR,by simpa only [hl] using hbefore⟩,?_⟩
    apply (mem_liftBits _ _ _ _ _ _).2
    exact ⟨rfl,hl.symm,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hl] using hafter⟩⟩
  · have hsub : guardFailures S F gi (_root_.OAI.Paper320.flip x {((w,c),a)}) v ⊆ guardFailures S F gj x v := by
      intro z hz
      obtain ⟨hR,hf⟩ := (mem_guardFailures S F gi _ v z).1 hz
      apply (mem_guardFailures S F gj x v z).2
      refine ⟨hR,?_⟩
      by_cases hp : (z,S.label v z)=(w,c)
      · have hzw : z=w := congrArg Prod.fst hp
        have hl : S.label v z=c := congrArg Prod.snd hp
        subst z
        rw [hl,child_flip_same] at hf
        cases hb : F gj (child x w c) with
        | true => simpa only [hl] using hb
        | false => exact False.elim (he ⟨hR,hl,hb,hf⟩)
      · rw [child_flip_other x w z c (S.label v z) a hp] at hf
        exact hF _ _ hg _ hf
    have hc : (guardFailures S F gi (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card ≤  q :=
      (Finset.card_le_card hsub).trans hj.2.2
    have hfalse : F ti (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v (!c₀))=false ∨
        F ui (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v c₀)=false := by
      cases hl : F ti (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v (!c₀)) with
      | false => exact Or.inl rfl
      | true =>
          cases hh : F ui (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v c₀) with
          | false => exact Or.inr rfl
          | true => exact False.elim (hoff ⟨hl,hh,hc⟩)
    apply Finset.mem_union_left
    rcases hfalse with hl | hh
    · have hp : (v,!c₀)=(w,c) := by
        by_contra hn
        rw [child_flip_other x w v c (!c₀) a hn] at hl
        have htrue := hF _ _ ht _ hj.1
        rw [hl] at htrue
        contradiction
      have hw : w=v := (congrArg Prod.fst hp).symm
      have hcc : c= !c₀ := (congrArg Prod.snd hp).symm
      subst w
      subst c
      rw [child_flip_same] at hl
      exact Finset.mem_union_left _ ((mem_liftBits _ _ _ _ _ _).2
        ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩⟩)
    · have hp : (v,c₀)=(w,c) := by
        by_contra hn
        rw [child_flip_other x w v c c₀ a hn] at hh
        have htrue := hF _ _ hu _ hj.2.1
        rw [hh] at htrue
        contradiction
      have hw : w=v := (congrArg Prod.fst hp).symm
      have hcc : c=c₀ := (congrArg Prod.snd hp).symm
      subst w
      subst c
      rw [child_flip_same] at hh
      exact Finset.mem_union_right _ ((mem_liftBits _ _ _ _ _ _).2
        ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩)











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
  (ti ui tj uj gi gj : L)
  (ht :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti tj)
  (hu :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ui uj)
  (hg :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (q : Nat) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (c₀ : Bool)
  (hj : @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tj uj gj q x v c₀),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRowBool L I V inst_2 S F ti ui gi q v c₀) Bool.false x)
    (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
        @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
          (fun (a b : Prod.{0, 0} V Bool) =>
            @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
              instDecidableEqBool a b)
          (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedBits L I V inst_1 F ti ui x v c₀)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits L I V inst_1 inst_2 S F gi gj x v)) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_down_cover
