-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_capacity_B_row
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:25:48.861892+00:00
-- url     : https://prove2.me/submissions/d5c2a2c9-7e29-4393-9ea3-55e12e067579

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_guardBits_card_le


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











theorem failed_card_le_outgoing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (failed S F j x v).card ≤  (outgoing S v).card := by
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.1⟩

theorem minmax_capacity_B_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (v : V) (da db degree target a : ℕ)
    (hcount : (failed S F j x v).card ≤  db) (hdb : db ≤  S.tolerance j)
    (hb : mm F (P.strongLower db) (P.strongUpper db) (child x v false) (child x v true)=true)
    (hda : da ≤  S.tolerance i) (hdba : db ≤  da)
    (ha : mm F (P.weakLower da) (P.weakUpper da) (child x v false) (child x v true)=true)
    (hdegree : (outgoing S v).card=degree)
    (htarget : (mmTargetBits F (P.weakLower db) (P.weakUpper db) x v).card ≤  target)
    (hA : ABound F (S.guard j) (S.guard i) a) :
    (flipsTo (parent S F i) false x).card ≤  target+if da=db ∧ db≤ degree then (degree-db)*a else 0 := by
  by_cases hslack : (failed S F j x v).card <  da
  · exact ((Finset.card_le_card (minmax_down_capacity_slack S F hF i j P x v da db hcount hdb hb hda ha hslack)).trans htarget).trans
      (Nat.le_add_right _ _)
  · have hdbcount : (failed S F j x v).card=db := by omega
    have hdaeq : da=db := by omega
    have hdbdegree : db≤ degree := by
      have hh := failed_card_le_outgoing S F j x v
      omega
    rw [if_pos ⟨hdaeq,hdbdegree⟩]
    have hg := guardBits_card_le S F i j x v a hA
    rw [hdbcount,hdegree] at hg
    exact (Finset.card_le_card (minmax_down_cover_capacity S F hF i j P x v db hcount hdb hb)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add htarget hg))



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
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (da db degree target a : Nat)
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
  (hA :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) a),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F i) Bool.false x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) target
      (@ite.{1} Nat (And (@Eq.{1} Nat da db) (@LE.le.{0} Nat instLENat db degree))
        (@instDecidableAnd (@Eq.{1} Nat da db) (@LE.le.{0} Nat instLENat db degree) (instDecidableEqNat da db)
          (Nat.decLe db degree))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree db) a)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_capacity_B_row
