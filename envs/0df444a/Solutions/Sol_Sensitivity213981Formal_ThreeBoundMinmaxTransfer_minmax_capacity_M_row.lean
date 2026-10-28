-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_capacity_M_row
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:26:04.586066+00:00
-- url     : https://prove2.me/submissions/1a978086-43cd-4101-a40e-c8823e5b155c

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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_down_capacity_slack
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_down_cover_capacity


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

theorem guardFailures_mono (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (g g' : L) (h : g' ≤  g)
    (x : ((V × Bool) × I) → Bool) (v : V) :
    guardFailures S F g x v ⊆ guardFailures S F g' x v := by
  intro w hw
  exact (mem_guardFailures S F g' x v w).2
    ⟨(mem_guardFailures S F g x v w).1 hw |>.1,
      hF _ _ h _ ((mem_guardFailures S F g x v w).1 hw).2⟩












@[simp] theorem mem_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passingGuards S F g x v ↔
      S.Adj v w ∧ F g (child x w (S.label v w)) = false := by
  simp only [passingGuards, outgoing, guardFailures, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases F g (child x w (S.label v w)) <;> simp

theorem card_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (passingGuards S F g x v).card =
      (outgoing S v).card - (guardFailures S F g x v).card := by
  apply Finset.card_sdiff_of_subset
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_guardFailures S F g x v w).1 hw |>.1⟩












































end
end ThreeBoundConditional




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Capacity and multiple-guard-gap refinements for exact-rank B/M transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundConditional
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem guard_gap_subset_passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gj gk : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    guardFailures S F gk x v \ guardFailures S F gj x v ⊆ passingGuards S F gj x v := by
  intro w hw
  obtain ⟨hk,hj⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨hR,htrue⟩ := (mem_guardFailures S F gk x v w).1 hk
  apply (mem_passingGuards S F gj x v w).2
  refine ⟨hR,?_⟩
  cases hh : F gj (child x w (S.label v w)) with
  | false => rfl
  | true => exact False.elim (hj ((mem_guardFailures S F gj x v w).2 ⟨hR,hh⟩))

theorem guardBits_card_selected (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj gk : L) (x : ((V × Bool) × I) → Bool) (v : V) (G : Finset V)
    (hG : G ⊆ passingGuards S F gj x v)
    (htrue : ∀ w ∈ G, F gk (child x w (S.label v w))=true)
    (a p : ℕ) (ha : ABound F gj gi a) (hp : PBound F gk gj gi p) :
    (ordinaryGuardBits S F gi gj x v).card ≤ 
      ((passingGuards S F gj x v).card-G.card)*a+G.card*min a p := by
  let A := passingGuards S F gj x v
  let W := fun w => liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)))
  have hsplit : A=(A\G) ∪ G := by
    ext w
    by_cases hw : w ∈ G
    · have hwa : w ∈ A := hG hw
      simp [hw,hwa]
    · simp only [Finset.mem_union,Finset.mem_sdiff,hw,not_false_eq_true,and_true,or_false]
  change (A.biUnion W).card ≤  (A.card-G.card)*a+G.card*min a p
  conv_lhs => rw [hsplit,Finset.union_biUnion]
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add
  · apply Finset.card_biUnion_le.trans
    calc
      _ ≤  ∑ _w ∈ A\G, a := by
        apply Finset.sum_le_sum
        intro w hw
        rw [card_liftBits]
        exact ha _ ((mem_passingGuards S F gj x v w).1 (Finset.mem_sdiff.mp hw).1).2
      _ = (A.card-G.card)*a := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [Finset.card_sdiff_of_subset (show G ⊆ A from hG)]
        simp
  · apply Finset.card_biUnion_le.trans
    calc
      _ ≤  ∑ _w ∈ G, min a p := by
        apply Finset.sum_le_sum
        intro w hw
        rw [card_liftBits]
        have hj := ((mem_passingGuards S F gj x v w).1 (hG hw)).2
        exact le_min (ha _ hj) (hp _ (htrue w hw) hj)
      _ = _ := by simp

theorem guardBits_card_gap (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (gi gj gk : L) (hg : gk ≤  gj) (x : ((V × Bool) × I) → Bool) (v : V)
    (gap a p : ℕ) (hgap : gap ≤  (guardFailures S F gk x v).card-(guardFailures S F gj x v).card)
    (ha : ABound F gj gi a) (hp : PBound F gk gj gi p) :
    (ordinaryGuardBits S F gi gj x v).card ≤ 
      ((outgoing S v).card-(guardFailures S F gj x v).card-gap)*a+gap*min a p := by
  have hsub := guardFailures_mono S F hF gj gk hg x v
  have hcount : gap ≤  (guardFailures S F gk x v\guardFailures S F gj x v).card := by
    rw [Finset.card_sdiff_of_subset hsub]
    exact hgap
  obtain ⟨G,hG,hcard⟩ := Finset.exists_subset_card_eq hcount
  have hpass := hG.trans (guard_gap_subset_passing S F gj gk x v)
  have htrue : ∀ w ∈ G, F gk (child x w (S.label v w))=true := by
    intro w hw
    exact ((mem_guardFailures S F gk x v w).1 (Finset.mem_sdiff.mp (hG hw)).1).2
  have hh := guardBits_card_selected S F gi gj gk x v G hpass htrue a p ha hp
  simpa only [hcard,card_passingGuards] using hh





theorem failed_card_le_outgoing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (failed S F j x v).card ≤  (outgoing S v).card := by
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.1⟩



theorem minmax_capacity_M_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (gk : L) (hg : gk ≤  S.guard j)
    (x : ((V × Bool) × I) → Bool) (v : V) (da db degree target gap a p : ℕ)
    (hcount : (failed S F j x v).card ≤  db) (hdb : db ≤  S.tolerance j)
    (hb : mm F (P.strongLower db) (P.strongUpper db) (child x v false) (child x v true)=true)
    (hda : da ≤  S.tolerance i) (hdba : db ≤  da)
    (ha : mm F (P.weakLower da) (P.weakUpper da) (child x v false) (child x v true)=true)
    (hdegree : (outgoing S v).card=degree)
    (htarget : (mmTargetBits F (P.weakLower db) (P.weakUpper db) x v).card ≤  target)
    (hgap : gap ≤  (guardFailures S F gk x v).card-(failed S F j x v).card)
    (hA : ABound F (S.guard j) (S.guard i) a) (hP : PBound F gk (S.guard j) (S.guard i) p) :
    (flipsTo (parent S F i) false x).card ≤ 
      target+if da=db ∧ db≤ degree then (degree-db-gap)*a+gap*min a p else 0 := by
  by_cases hslack : (failed S F j x v).card <  da
  · exact ((Finset.card_le_card (minmax_down_capacity_slack S F hF i j P x v da db hcount hdb hb hda ha hslack)).trans htarget).trans
      (Nat.le_add_right _ _)
  · have hdbcount : (failed S F j x v).card=db := by omega
    have hdaeq : da=db := by omega
    have hdbdegree : db≤ degree := by
      have hh := failed_card_le_outgoing S F j x v
      omega
    rw [if_pos ⟨hdaeq,hdbdegree⟩]
    have hgcard := guardBits_card_gap S F hF (S.guard i) (S.guard j) gk hg x v gap a p hgap hA hP
    change (guardBits S F i j x v).card ≤ 
      ((outgoing S v).card-(failed S F j x v).card-gap)*a+gap*min a p at hgcard
    rw [hdbcount,hdegree] at hgcard
    exact (Finset.card_le_card (minmax_down_cover_capacity S F hF i j P x v db hcount hdb hb)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add htarget hgcard))

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
  (i j : L)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F i j)
  (gk : L)
  (hg :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j))
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (da db degree target gap a p : Nat)
  (hcount :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x v)) db)
  (hdb : @LE.le.{0} Nat instLENat db (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j))
  (hb :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm L I F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P db)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P db)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.true))
      Bool.true)
  (hda : @LE.le.{0} Nat instLENat da (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S i))
  (hdba : @LE.le.{0} Nat instLENat db da)
  (ha :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm L I F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P da)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P da)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.true))
      Bool.true)
  (hdegree :
    @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (htarget :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits L I V inst_1 F
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
            S F i j P db)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
            S F i j P db)
          x v))
      target)
  (hgap :
    @LE.le.{0} Nat instLENat gap
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gk x v))
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x v))))
  (hA :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) a)
  (hP :
    @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F gk
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) p),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F i) Bool.false x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) target
      (@ite.{1} Nat (And (@Eq.{1} Nat da db) (@LE.le.{0} Nat instLENat db degree))
        (@instDecidableAnd (@Eq.{1} Nat da db) (@LE.le.{0} Nat instLENat db degree) (instDecidableEqNat da db)
          (Nat.decLe db degree))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree db) gap)
            a)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) gap (@Min.min.{0} Nat instMinNat a p)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_capacity_M_row
