-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxHybrid.upper_of_a_core
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:46:31.818912+00:00
-- url     : https://prove2.me/submissions/3eb52a38-9756-4659-a363-dd7dd82a8d35

import Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_dCore_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_pCore_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_rawBExpr_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_rawMExpr_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_rawBExpr_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_rawMExpr_bound


namespace Sensitivity213981Formal
section
/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]





































theorem d_of_m_add_p (F : L → (I → Bool) → Bool) (i j k l : L) (m p : ℕ)
    (hm : MBound F i j k m) (hp : PBound F j k l p) : DBound F i j k l (m+p) := by
  intro x hx hy
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hm x hx hy) (hp x hx hy))



























end
end ThreeBoundProfiles






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]









theorem next_val (j : Fin n) (h : j.val+1 <  n) : (next j).val = j.val+1 := by
  simp [next,h]

theorem self_le_next (j : Fin n) : j ≤  next j := by
  unfold next
  split_ifs <;> simp only [Fin.le_iff_val_le_val] <;> omega



theorem next_le_of_lt (i j : Fin n) (h : i <  j) : next i ≤  j := by
  have hi : i.val+1 <  n := by have hj := j.isLt; exact lt_of_le_of_lt h hj
  change (next i).val ≤  j.val
  rw [next_val i hi]
  exact h



theorem next_lt_n_of_lt (i j : Fin n) (h : i <  j) : i.val+1 <  n :=
  lt_of_le_of_lt h j.isLt



















































end
end ThreeBoundFullProfile




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Symbolic transcription of graded2_union_recurrence.py, with the ordinary
q=1, three-positive cap corrected to marked[6]+2, the established general
bound. This correction changes no coordinate of the first endpoint's four
numerical phases, because every ordinary q=1 fallback there is absent.
The formulas are homogeneous natural arithmetic expressions. This module
defines the numeric raw transfer; its semantic raw-A/M/P/D obligations are
separate theorems about the actual Boolean parent. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile











@[simp] theorem eval_min {n : ℕ} (v : Profile n) (a b : Expr n) :
    (min a b).eval v = min (a.eval v) (b.eval v) := rfl






































































end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Literal parent A entries may be proved on a small covering set of intervals.
All remaining coordinates then use scalar conditional bounds. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxHybrid
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxRank (fullBExpr fullMExpr)
open ThreeBoundMinmaxNumeric (pCore dCore)
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]









theorem upper_of_a_core (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → ThreeBoundMinmaxNumeric.Entry)
    (P : ∀ i j : Fin n, i ≤  j → PairData S F i j)
    (hm : ∀ (i j : Fin n) (hij : i ≤  j),
      ThreeBoundMinmaxNumeric.EntryMatch S F i j (P i j hij) (recipe i) (recipe j))
    (degree pcross : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (pcross+1))
    (v w : Profile n) (hv : Upper F v)
    (hA : ∀ i j : Fin n, i ≤  j → ABound (parent S F) i j (w (.a i j)))
    (hc : CoreBounds degree pcross recipe v w) : Upper (parent S F) w := by
  have hM : ∀ i j : Fin n, i ≤  j → j.val+1< n →
      MBound (parent S F) i j (next j) (w (.m i j)) := by
    intro i j hij hjn x hxj hxk
    have hb := ThreeBoundMinmaxNumeric.rawMExpr_bound S F hF recipe i j (next j)
      (P i j hij) (P j (next j) (self_le_next j))
      (hm i j hij) (hm j (next j) (self_le_next j)) degree hd v hv
    have hr := ThreeBoundMinmaxRank.rawMExpr_bound S F hF i j (next j)
      (P i j hij) (P j (next j) (self_le_next j))
      (recipe i) (recipe j) (recipe (next j)) (hm i j hij) (hm j (next j) (self_le_next j))
      degree hd v hv
    have hh : (flipsTo (parent S F i) false x).card ≤ 
        (fullMExpr n degree (recipe i) (recipe j) (recipe (next j))).eval v := by
      rw [fullMExpr,eval_min]
      exact le_min (hb x hxj hxk) (hr x hxj hxk)
    exact hh.trans (hc.m i j hij hjn)
  have hP : ∀ j l : Fin n, j <  l →
      PBound (parent S F) j (next j) l (w (.p j l)) := by
    intro j l hjl
    have hp := ThreeBoundMinmaxNumeric.pCore_bound S hT F hF recipe j (next j) l
      (P j (next j) (self_le_next j)) (P (next j) l (next_le_of_lt j l hjl))
      (hm j (next j) (self_le_next j)) (hm (next j) l (next_le_of_lt j l hjl))
      pcross (w (.a (next j) l)) hcap v hv (hA (next j) l (next_le_of_lt j l hjl))
    intro x hxj hxk
    exact (hp x hxj hxk).trans (hc.p j l hjl)
  intro coord
  cases coord with
  | a i j => exact hA i j
  | b i j =>
      intro hij x hxj
      have hb := ThreeBoundMinmaxNumeric.rawBExpr_bound S F hF recipe i j
        (P i j hij) (hm i j hij) degree hd v hv
      have hr := ThreeBoundMinmaxRank.rawBExpr_bound S F hF i j
        (P i j hij) (recipe i) (recipe j) (hm i j hij) degree hd v hv
      have hh : (flipsTo (parent S F i) false x).card ≤ 
          (fullBExpr n degree (recipe i) (recipe j)).eval v := by
        rw [fullBExpr,eval_min]
        exact le_min (hb x hxj) (hr x hxj)
      exact hh.trans (hc.b i j hij)
  | m i j => exact hM i j
  | p j l => exact hP j l
  | d i j l =>
      intro hij hjl
      have hd' := d_of_m_add_p (parent S F) i j (next j) l _ _
        (hM i j hij (next_lt_n_of_lt j l hjl)) (hP j l hjl)
      have hh := ThreeBoundMinmaxNumeric.dCore_bound S hT F hF recipe i j (next j) l
        (P i j hij) (P j (next j) (self_le_next j)) (P (next j) l (next_le_of_lt j l hjl))
        (hm i j hij) (hm j (next j) (self_le_next j)) (hm (next j) l (next_le_of_lt j l hjl))
        degree (w (.m i j)+w (.p j l)) hd v hv hd'
      intro x hxj hxk
      exact (hh x hxj hxk).trans (hc.d i j l hij hjl)

end
end ThreeBoundMinmaxHybrid




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V)
  (hT :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S))
  (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry)
  (P :
    (i j : Fin n) →
      @LE.le.{0} (Fin n) (@instLEFin n) i j →
        @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (hm :
    ∀ (i j : Fin n) (hij : @LE.le.{0} (Fin n) (@instLEFin n) i j),
      @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j (P i j hij) (recipe i) (recipe j))
  (degree pcross : Nat)
  (hd :
    ∀ (w : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing (Fin n) I V inst_1 S w))
        degree)
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pcross
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (v w : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hA :
    ∀ (i j : Fin n),
      @LE.le.{0} (Fin n) (@instLEFin n) i j →
        @Sensitivity213981Formal.ThreeBoundProfiles.ABound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
          (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) i j
          (w (@Sensitivity213981Formal.ThreeBoundFullProfile.Coord.a n i j)))
  (hc : @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.CoreBounds n degree pcross recipe v w),
  @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) w := @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.upper_of_a_core
