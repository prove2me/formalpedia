-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.rawBExpr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:24:16.729693+00:00
-- url     : https://prove2.me/submissions/47ac9338-b740-4546-9597-2a9e7edf0623

import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_B_row
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_minusExpr_bound


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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile
















@[simp] theorem maximum_cons (x : ℕ) (xs : List ℕ) :
    maximum (x::xs) = max x (maximum xs) := rfl

theorem le_maximum_of_mem {xs : List ℕ} {x : ℕ} (h : x ∈ xs) :
    x ≤  maximum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)



theorem Expr.eval_maximum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.maximum es).eval v = ThreeBoundNumeric.maximum (es.map (fun e => e.eval v)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.maximum, List.foldr_cons, Expr.eval,
      List.map_cons, maximum_cons] using congrArg (Nat.max (e.eval v)) ih



















end ThreeBoundNumeric



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








@[simp] theorem eval_add {n : ℕ} (v : Profile n) (a b : Expr n) :
    (a+b).eval v = a.eval v+b.eval v := rfl

@[simp] theorem eval_mul {n : ℕ} (v : Profile n) (k : ℕ) (a : Expr n) :
    (k*a).eval v = k*a.eval v := rfl

@[simp] theorem eval_max {n : ℕ} (v : Profile n) (a b : Expr n) :
    (max a b).eval v = max (a.eval v) (b.eval v) := rfl
@[simp] theorem eval_zero {n : ℕ} (v : Profile n) : (0 : Expr n).eval v=0 := rfl




































































end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Semantic interpretation of interval maxima in the transfer formula. -/


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile





variable {n : ℕ} {I : Type} [Fintype I]

theorem aExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤  j) :
    ABound F i j ((aExpr n i.val j.val).eval v) := by
  simpa only [aExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.a i j) hij

theorem bExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤  j) :
    BBound F i j ((bExpr n i.val j.val).eval v) := by
  simpa only [bExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.b i j) hij







end ThreeBoundNumeric





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Interpreting the exact numeric q2 head-cost expressions on actual heads. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundHeadExpressions
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]



theorem minusExpr_bound_all (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (i j k : Fin n) (hij : i ≤  j) :
    MBound F i j k ((minusExpr n i.val j.val k.val).eval v) := by
  by_cases hjk : j <  k
  · exact minusExpr_bound F v hv i j k hij hjk
  · intro x hj hk
    have he := hF k j (le_of_not_gt hjk) x hj
    rw [hk] at he
    contradiction





















end
end ThreeBoundHeadExpressions






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The exact link between finite numeric min/max entries and Boolean recipes. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]





















theorem eval_ite {m : ℕ} (v : Profile m) (p : Prop) [Decidable p] (a b : Expr m) :
    (if p then a else b).eval v=if p then a.eval v else b.eval v := by
  split_ifs <;> rfl

end
end ThreeBoundMinmaxNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual Boolean semantics of the numeric min/max raw-B expression. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rawBExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v) :
    BBound (parent S F) i j ((rawBExpr n degree (recipe i) (recipe j)).eval v) := by
  intro x hx
  obtain ⟨w,hcount,hwin⟩ := (parent_true_iff S F j x).1 hx
  let d := (failed S F j x w).card
  have hdq : d ≤  S.tolerance j := hcount
  have hdi : d ≤  S.tolerance i := hdq.trans P.tolerances
  have hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true := by
    simpa only [P.strongDef] using hwin
  have ha := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hb0 := bExpr_bound F v hv (P.weakLower d) (P.strongLower d) (P.lowerOrder d hdq)
  have hb1 := bExpr_bound F v hv (P.weakLower d) (P.strongUpper d)
    ((P.lowerOrder d hdq).trans (P.strongLowerUpper d hdq))
  have hbu := bExpr_bound F v hv (P.weakUpper d) (P.strongUpper d) (P.upperOrder d hdq)
  have hm0 := minusExpr_bound_all F hF v hv (P.weakLower d) (P.strongLower d) (P.weakUpper d) (P.lowerOrder d hdq)
  have hh := minmax_B_row S F hF i j P x w d rfl hdq hstrong _ _ _ _ _ ha hb0 hb1 hbu hm0
  rw [hd w] at hh
  have hgate : ((recipe i).tolerance ≤  d ∨ (recipe j).lowerAt d< (recipe i).lowerAt (d+1) ∨
      (recipe j).upperAt d< (recipe i).upperAt (d+1)) ↔
      ¬(d+1 ≤  S.tolerance i ∧ P.weakLower (d+1) ≤  P.strongLower d ∧ P.weakUpper (d+1) ≤  P.strongUpper d) := by
    rw [← hm.weakTolerance]
    by_cases hnext : d+1 ≤  S.tolerance i
    · rw [← hm.weakLower (d+1) hnext,← hm.weakUpper (d+1) hnext,
        ← hm.strongLower d hdq,← hm.strongUpper d hdq]
      change (_ ∨ (P.strongLower d).val< (P.weakLower (d+1)).val ∨
        (P.strongUpper d).val< (P.weakUpper (d+1)).val) ↔
        ¬(_ ∧ (P.weakLower (d+1)).val ≤  (P.strongLower d).val ∧
          (P.weakUpper (d+1)).val ≤  (P.strongUpper d).val)
      omega
    · have hle : S.tolerance i ≤  d := by omega
      simp only [hle,true_or,hnext,false_and,not_false_eq_true]
  have hrow : (flipsTo (parent S F i) false x).card ≤ 
      (max (bExpr n ((recipe i).lowerAt d) ((recipe j).lowerAt d)+
        bExpr n ((recipe i).lowerAt d) ((recipe j).upperAt d))
        (if (recipe j).lowerAt d< (recipe i).upperAt d then
          bExpr n ((recipe i).upperAt d) ((recipe j).upperAt d)+
          minusExpr n ((recipe i).lowerAt d) ((recipe j).lowerAt d) ((recipe i).upperAt d) else 0)+
        if (recipe i).tolerance ≤  d ∨ (recipe j).lowerAt d< (recipe i).lowerAt (d+1) ∨
          (recipe j).upperAt d< (recipe i).upperAt (d+1)
        then (degree-d)*aExpr n (recipe j).guard (recipe i).guard else 0).eval v := by
    by_cases hs : d+1 ≤  S.tolerance i ∧ P.weakLower (d+1) ≤  P.strongLower d ∧ P.weakUpper (d+1) ≤  P.strongUpper d
    · rw [if_neg (fun h => (hgate.mp h) hs)]
      simpa only [if_pos hs,eval_add,eval_max,eval_mul,eval_zero,eval_ite,Fin.lt_def,
        hm.weakLower d hdi,hm.weakUpper d hdi,hm.strongLower d hdq,hm.strongUpper d hdq,
        hm.weakGuard,hm.strongGuard] using hh
    · rw [if_pos (hgate.mpr hs)]
      simpa only [if_neg hs,eval_add,eval_max,eval_mul,eval_zero,eval_ite,Fin.lt_def,
        hm.weakLower d hdi,hm.weakUpper d hdi,hm.strongLower d hdq,hm.strongUpper d hdq,
        hm.weakGuard,hm.strongGuard] using hh
  apply hrow.trans
  simp only [rawBExpr,Expr.eval_maximum,List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  exact ⟨d,List.mem_range.mpr (by rw [← hm.strongTolerance]; omega),rfl⟩

end
end ThreeBoundMinmaxNumeric



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry) (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P (recipe i) (recipe j))
  (degree : Nat)
  (hd :
    ∀ (w : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing (Fin n) I V inst_1 S w))
        degree)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v),
  @Sensitivity213981Formal.ThreeBoundProfiles.BBound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) i j
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.rawBExpr n degree (recipe i) (recipe j))) := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.rawBExpr_bound
