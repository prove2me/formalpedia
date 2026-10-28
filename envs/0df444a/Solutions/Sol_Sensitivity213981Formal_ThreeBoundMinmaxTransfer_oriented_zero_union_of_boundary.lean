-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_zero_union_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:25:56.897969+00:00
-- url     : https://prove2.me/submissions/fb055210-7fea-4084-bd55-4f534a9eefda

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_repair_cases
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_union_guard_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_union_subset
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_union_target_bound


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

theorem guardFailures_mono (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (g g' : L) (h : g' ≤  g)
    (x : ((V × Bool) × I) → Bool) (v : V) :
    guardFailures S F g x v ⊆ guardFailures S F g' x v := by
  intro w hw
  exact (mem_guardFailures S F g' x v w).2
    ⟨(mem_guardFailures S F g x v w).1 hw |>.1,
      hF _ _ h _ ((mem_guardFailures S F g x v w).1 hw).2⟩








































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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]















theorem strict_no_repair (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V)
    (hoff : ¬ordinaryRow S F t g 0 x v)
    (ht : ¬StrictTargetCandidate S F t g x v)
    (hg : ¬StrictGuardCandidate S F t g x v) :
    flipsTo (ordinaryRowBool S F t g 0 v) true x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F t g 0 _ v).1 (Finset.mem_filter.mp ha).2
  rcases strict_repair_cases S F t g x v w c a hoff hon with hh | hh
  · exact ht ⟨c,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  · exact hg ⟨hh.1,w,hh.2.1⟩





















end
end ThreeBoundConditional



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Shared actual-predicate interface for symmetric min/max transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



theorem mm_true (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=true ↔ F t x=true ∧ F t y=true ∧ (F u x=true ∨ F u y=true) := by
  simp only [mm,Bool.and_eq_true,Bool.or_eq_true,and_assoc]















end
end ThreeBoundMinmaxTransfer




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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]



















theorem true_false_lt (F : L → (I → Bool) → Bool) (hF : Nested F)
    (j k : L) (x : I → Bool) (hj : F j x=true) (hk : F k x=false) : j< k := by
  by_contra hn
  have he := hF _ _ (le_of_not_gt hn) _ hj
  rw [hk] at he
  contradiction





end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The oriented-row estimates applied to actual graded min/max parents. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_orientation (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (h : mm F t u (child x w false) (child x w true)=true) :
    ∃ c : Bool, F t (child x w (!c))=true ∧ F u (child x w c)=true := by
  obtain ⟨hl,hr,hupper⟩ := (mm_true F t u _ _).1 h
  rcases hupper with hh | hh
  · exact ⟨false,hr,hh⟩
  · exact ⟨true,hl,hh⟩





end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Strict conditional union transfer for a symmetric min/max middle witness.
The target-repair branch chooses its orientation after locating the missing child. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem oriented_zero_union_of_boundary (S : Stage L I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (G : (((V × Bool) × I) → Bool) → Bool)
    (ti ui tj uj tk uk tl gi gj gk gl : L)
    (htiu : ti ≤  ui) (htij : ti ≤  tj) (huij : ui ≤  uj)
    (hujl : uj ≤  tl) (htkl : tk ≤  tl) (hukl : uk ≤  tl)
    (hgjgi : gj ≤  gi) (hgkgj : gk ≤  gj) (hglgk : gl ≤  gk)
    (hgil : gi ≤  tl) (hgli : gl ≤  ti)
    (degree b0 b1 a dt dg R : ℕ)
    (hb0 : BBound F ti tl b0) (hb1 : BBound F ui tl b1) (ha : ABound F gl gi a)
    (hdt : DBound F ti tj tk tl dt) (hdg : DBound F gl gk gj gi dg)
    (x : ((V × Bool) × I) → Bool) (v : V) (hd : (outgoing S v).card=degree)
    (hjmm : mm F tj uj (child x v false) (child x v true)=true)
    (hjguard : (guardFailures S F gj x v).card=0)
    (hk : ∀ c, ¬orientedRow S F tk uk gk 0 x v c)
    (haccept : ∀ c y, orientedRow S F ti ui gi 0 y v c → G y=true)
    (hR : ∀ c, orientedRow S F tj uj gj 0 x v c →
      (flipsTo (orientedRowBool S F ti ui gi 0 v c) false x).card ≤  R) :
    (flipsTo G false x ∪ flipsTo (ordinaryParent S F tl gl 0) true x).card ≤ 
      max R (max (if tj< tk then b1+degree*a+dt else 0)
        (if gk< gj then b0+b1+(degree-1)*a+dg else 0)) := by
  have hweak : ∀ c, orientedRow S F tj uj gj 0 x v c → orientedRow S F ti ui gi 0 x v c := by
    intro c hc
    exact ⟨hF _ _ htij _ hc.1,hF _ _ huij _ hc.2.1,
      (Finset.card_le_card (guardFailures_mono S F hF gi gj hgjgi x v)).trans hc.2.2⟩
  have hvl : ¬ordinaryRow S F tl gl 0 x v := by
    intro hr
    apply hk false
    exact ⟨hF _ _ htkl _ (hr.1 true),hF _ _ hukl _ (hr.1 false),
      (Finset.card_le_card (guardFailures_mono S F hF gk gl hglgk x v)).trans hr.2⟩
  obtain ⟨cMain,hloMain,hhiMain⟩ := mm_orientation F tj uj x v hjmm
  have hjMain : orientedRow S F tj uj gj 0 x v cMain := ⟨hloMain,hhiMain,hjguard.le⟩
  by_cases hcT : StrictTargetCandidate S F tl gl x v
  · obtain ⟨c₀,hfalse,hother,hgl⟩ := hcT
    have hlow : F tj (child x v c₀)=true := by
      have hh := (mm_true F tj uj _ _).1 hjmm
      cases c₀
      · exact hh.1
      · exact hh.2.1
    have hhigh : F uj (child x v (!c₀))=true :=
      hF _ _ hujl _ (hother (!c₀) (by cases c₀ <;> decide))
    have hj : orientedRow S F tj uj gj 0 x v (!c₀) := by
      exact ⟨by simpa only [Bool.not_not] using hlow,hhigh,hjguard.le⟩
    have hglk : guardFailures S F gk x v=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hh := guardFailures_mono S F hF gk gl hglgk x v hw
      rw [hgl] at hh
      exact Finset.notMem_empty _ hh
    have hkt : F tk (child x v c₀)=false := by
      cases h : F tk (child x v c₀) with
      | false => rfl
      | true =>
        apply False.elim
        apply hk (!c₀)
        refine ⟨by simpa only [Bool.not_not] using h,?_,by simp [hglk]⟩
        exact hF _ _ hukl _ (hother (!c₀) (by cases c₀ <;> decide))
    have hlt : tj< tk := true_false_lt F hF tj tk _ hlow hkt
    have hsub := oriented_union_subset S hT F hF G ti ui tl gi gl htiu hgil hgli x v (!c₀) (haccept (!c₀))
    have hbound := oriented_union_target_bound S F hF ti ui tl gi gl degree b1 a dt hb1 ha
      x v c₀ hd (hweak (!c₀) hj) hfalse hother hgl (hdt _ hlow hkt)
    apply ((Finset.card_le_card hsub).trans hbound).trans
    rw [if_pos hlt]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · by_cases hcG : StrictGuardCandidate S F tl gl x v
    · obtain ⟨ht,w₀,hgl⟩ := hcG
      have hwmem : w₀ ∈ guardFailures S F gl x v := by rw [hgl]; simp
      have hadj := ((mem_guardFailures S F gl x v w₀).1 hwmem).1
      have hjoff : F gj (child x w₀ (S.label v w₀))=false := by
        cases h : F gj (child x w₀ (S.label v w₀)) with
        | false => rfl
        | true =>
          have hh := (mem_guardFailures S F gj x v w₀).2 ⟨hadj,h⟩
          rw [Finset.card_eq_zero.mp hjguard] at hh
          exact False.elim (Finset.notMem_empty _ hh)
      have hkon : F gk (child x w₀ (S.label v w₀))=true := by
        cases h : F gk (child x w₀ (S.label v w₀)) with
        | true => rfl
        | false =>
          have hempty : guardFailures S F gk x v=∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro w hw
            have hglw := guardFailures_mono S F hF gk gl hglgk x v hw
            rw [hgl,Finset.mem_singleton] at hglw
            subst w
            have hh := ((mem_guardFailures S F gk x v w₀).1 hw).2
            rw [h] at hh
            contradiction
          apply False.elim
          apply hk cMain
          exact ⟨hF _ _ htkl _ (ht (!cMain)),hF _ _ hukl _ (ht cMain),by simp [hempty]⟩
      have hlt : gk< gj := true_false_lt F hF gk gj _ hkon hjoff
      have hlocal : (flipsTo (F gi) true (child x w₀ (S.label v w₀)) ∪
          flipsTo (F gl) false (child x w₀ (S.label v w₀))).card ≤  dg := by
        simpa only [Finset.union_comm] using hdg _ hkon hjoff
      have hsub := oriented_union_subset S hT F hF G ti ui tl gi gl htiu hgil hgli x v cMain (haccept cMain)
      have hbound := oriented_union_guard_bound S F hF ti ui tl gi gl degree b0 b1 a dg hb0 hb1 ha
        x v w₀ cMain hd (hweak cMain hjMain) ht hgl hlocal
      apply ((Finset.card_le_card hsub).trans hbound).trans
      rw [if_pos hlt]
      exact (le_max_right _ _).trans (le_max_right _ _)
    · have hsub := oriented_union_subset S hT F hF G ti ui tl gi gl htiu hgil hgli x v cMain (haccept cMain)
      rw [strict_no_repair S F tl gl x v hvl hcT hcG,Finset.union_empty] at hsub
      exact ((Finset.card_le_card hsub).trans (hR cMain hjMain)).trans (le_max_left _ _)



end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (hT :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S))
  (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (G : (Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) → Bool) (ti ui tj uj tk uk tl gi gj gk gl : L)
  (htiu :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti ui)
  (htij :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti tj)
  (huij :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ui uj)
  (hujl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      uj tl)
  (htkl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tk tl)
  (hukl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      uk tl)
  (hgjgi :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (hgkgj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk gj)
  (hglgk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl gk)
  (hgil :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gi tl)
  (hgli :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl ti)
  (degree b0 b1 a dt dg R : Nat) (hb0 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tl b0)
  (hb1 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ui tl b1)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gl gi a)
  (hdt : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F ti tj tk tl dt)
  (hdg : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F gl gk gj gi dg)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V)
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hjmm :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm L I F tj uj
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.true))
      Bool.true)
  (hjguard :
    @Eq.{1} Nat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gj x v))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (hk :
    ∀ (c : Bool),
      Not
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tk uk gk
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c))
  (haccept :
    ∀ (c : Bool) (y : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool),
      @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F ti ui gi
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) y v c →
        @Eq.{1} Bool (G y) Bool.true)
  (hR :
    ∀ (c : Bool),
      @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tj uj gj
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
            (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
              (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype)
                inst_1)
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRowBool L I V inst_2 S F ti ui gi
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v c)
              Bool.false x))
          R),
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
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1) G
          Bool.false x)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tl gl
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          Bool.true x)))
    (@Max.max.{0} Nat Nat.instMax R
      (@Max.max.{0} Nat Nat.instMax
        (@ite.{1} Nat
          (@LT.lt.{0} L
            (@Preorder.toLT.{0} L
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
            tj tk)
          (@LinearOrder.toDecidableLT.{0} L inst tj tk)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b1
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) degree a))
            dt)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@ite.{1} Nat
          (@LT.lt.{0} L
            (@Preorder.toLT.{0} L
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
            gk gj)
          (@LinearOrder.toDecidableLT.{0} L inst gk gj)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b0 b1)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                a))
            dg)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_zero_union_of_boundary
