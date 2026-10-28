-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_pairM_row
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:15:26.934128+00:00
-- url     : https://prove2.me/submissions/3bcfea23-81f6-4c1b-8bdd-17b71550efe7

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinaryGuardBits_card_le
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinaryGuardBits_card_special
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_down_cover


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
/- Actual min/max downward transfer, with the upper-child improvement and
exact next-tier guard-destruction gate. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









theorem orientedBits_card (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a b : ℕ)
    (ha : (flipsTo (F t) false (child x w (!c))).card ≤  a)
    (hb : (flipsTo (F u) false (child x w c)).card ≤  b) :
    (orientedBits F t u x w c).card ≤  a+b := by
  exact (Finset.card_union_le _ _).trans (by simpa only [card_liftBits] using Nat.add_le_add ha hb)













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
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
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

theorem orientedBits_conditional_card (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj tk uk : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (hj0 : F tj (child x v (!c))=true) (hj1 : F uj (child x v c)=true)
    (hmiss : F tk (child x v (!c))=false ∨ F uk (child x v c)=false)
    (m0 m1 b0 b1 : ℕ) (hm0 : MBound F ti tj tk m0) (hm1 : MBound F ui uj uk m1)
    (hb0 : BBound F ti tk b0) (hb1 : BBound F ui uk b1) :
    (orientedBits F ti ui x v c).card ≤  pairMTarget tj uj tk uk m0 m1 b0 b1 := by
  cases hk0 : F tk (child x v (!c)) <;> cases hk1 : F uk (child x v c)
  · have ht := true_false_lt F hF tj tk _ hj0 hk0
    have hu := true_false_lt F hF uj uk _ hj1 hk1
    have hh := orientedBits_card F ti ui x v c m0 m1 (hm0 _ hj0 hk0) (hm1 _ hj1 hk1)
    exact hh.trans (by unfold pairMTarget; rw [if_pos ⟨ht,hu⟩]; exact le_max_left _ _)
  · have ht := true_false_lt F hF tj tk _ hj0 hk0
    have hh := orientedBits_card F ti ui x v c m0 b1 (hm0 _ hj0 hk0) (hb1 _ hk1)
    exact hh.trans (by unfold pairMTarget; rw [if_pos ht]; exact (le_max_left _ _).trans (le_max_right _ _))
  · have hu := true_false_lt F hF uj uk _ hj1 hk1
    have hh := orientedBits_card F ti ui x v c b0 m1 (hb0 _ hk0) (hm1 _ hj1 hk1)
    exact hh.trans (by unfold pairMTarget; rw [if_pos hu]; exact (le_max_right _ _).trans (le_max_right _ _))
  · rcases hmiss with he | he <;> simp_all

/-- Exact oriented conditional transfer for a middle witness with d guards. -/
theorem oriented_pairM_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tj uj tk uk gi gj gk : L)
    (htij : ti ≤  tj) (huij : ui ≤  uj) (hgij : gj ≤  gi) (hgkj : gk ≤  gj)
    (q degree : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (hj : orientedRow S F tj uj gj q x v c)
    (hcount : (guardFailures S F gj x v).card=q)
    (hk : ¬ orientedRow S F tk uk gk q x v c)
    (hd : (outgoing S v).card=degree)
    (a m0 m1 b0 b1 p : ℕ) (ha : ABound F gj gi a)
    (hm0 : MBound F ti tj tk m0) (hm1 : MBound F ui uj uk m1)
    (hb0 : BBound F ti tk b0) (hb1 : BBound F ui uk b1) (hp : PBound F gk gj gi p) :
    (flipsTo (orientedRowBool S F ti ui gi q v c) false x).card ≤ 
      pairMCost degree q tj uj tk uk gj gk a m0 m1 b0 b1 p := by
  have hcover := Finset.card_le_card (oriented_down_cover S F hF ti ui tj uj gi gj htij huij hgij q x v c hj)
  have hsplit := hcover.trans (Finset.card_union_le _ _)
  by_cases hmiss : F tk (child x v (!c))=false ∨ F uk (child x v c)=false
  · have hgap : tj< tk ∨ uj< uk := hmiss.elim
      (fun he => Or.inl (true_false_lt F hF tj tk _ hj.1 he))
      (fun he => Or.inr (true_false_lt F hF uj uk _ hj.2.1 he))
    have ht := orientedBits_conditional_card F hF ti ui tj uj tk uk x v c hj.1 hj.2.1
      hmiss m0 m1 b0 b1 hm0 hm1 hb0 hb1
    have hg := ordinaryGuardBits_card_le S F gi gj x v a ha
    rw [hd,hcount] at hg
    exact (hsplit.trans (Nat.add_le_add ht hg)).trans (by
      unfold pairMCost
      rw [if_pos hgap]
      exact le_max_left _ _)
  · have hk0 : F tk (child x v (!c))=true := by cases he : F tk (child x v (!c)) <;> simp_all
    have hk1 : F uk (child x v c)=true := by cases he : F uk (child x v c) <;> simp_all
    have hguard : q <  (guardFailures S F gk x v).card := by
      by_contra hn
      exact hk ⟨hk0,hk1,by omega⟩
    have hlt : gk< gj := by
      apply lt_of_le_of_ne hgkj
      intro he
      rw [he,hcount] at hguard
      omega
    have hex : ∃ w ∈ guardFailures S F gk x v, w ∉ guardFailures S F gj x v := by
      by_contra hn
      have hsub : guardFailures S F gk x v ⊆ guardFailures S F gj x v := by
        intro w hw
        by_contra hjw
        exact hn ⟨w,hw,hjw⟩
      have hh := Finset.card_le_card hsub
      omega
    obtain ⟨w,hwk,hwj⟩ := hex
    obtain ⟨hR,hktrue⟩ := (mem_guardFailures S F gk x v w).1 hwk
    have hjfalse : F gj (child x w (S.label v w))=false := by
      cases he : F gj (child x w (S.label v w)) with
      | false => rfl
      | true => exact False.elim (hwj ((mem_guardFailures S F gj x v w).2 ⟨hR,he⟩))
    have hpw := (mem_passingGuards S F gj x v w).2 ⟨hR,hjfalse⟩
    have hg := ordinaryGuardBits_card_special S F gi gj gk x v w a p ha hp hpw hktrue
    rw [hd,hcount] at hg
    have ht := orientedBits_card F ti ui x v c b0 b1 (hb0 _ hk0) (hb1 _ hk1)
    exact (hsplit.trans (Nat.add_le_add ht hg)).trans (by
      unfold pairMCost
      rw [if_pos hlt]
      have he : b0+b1+((degree-q-1)*a+p)=b0+b1+(degree-q-1)*a+p := by omega
      rw [he]
      exact le_max_right _ _)

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
  (ti ui tj uj tk uk gi gj gk : L)
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
  (hgij :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (hgkj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk gj)
  (q degree : Nat) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (c : Bool)
  (hj : @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tj uj gj q x v c)
  (hcount :
    @Eq.{1} Nat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gj x v)) q)
  (hk : Not (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tk uk gk q x v c))
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (a m0 m1 b0 b1 p : Nat) (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj gi a)
  (hm0 : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F ti tj tk m0)
  (hm1 : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F ui uj uk m1)
  (hb0 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tk b0)
  (hb1 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ui uk b1)
  (hp : @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F gk gj gi p),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRowBool L I V inst_2 S F ti ui gi q v c) Bool.false
        x))
    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.pairMCost L inst degree q tj uj tk uk gj gk a m0 m1 b0 b1 p) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_pairM_row
