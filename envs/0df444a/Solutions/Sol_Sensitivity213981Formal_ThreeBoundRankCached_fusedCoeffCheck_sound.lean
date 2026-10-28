-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankCached.fusedCoeffCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:58:28.535038+00:00
-- url     : https://prove2.me/submissions/b462ce5d-607a-4eb9-8c13-be13c78925cd

import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankFusedCoefficients
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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



@[simp] theorem eval_max {n : ℕ} (v : Profile n) (a b : Expr n) :
    (max a b).eval v = max (a.eval v) (b.eval v) := rfl





































































end ThreeBoundNumeric



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
/- One rank-state traversal computes all three head-hit coefficients.
Impossible kinds have an identically zero maximum and need no second scan. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Expr bExpr aExpr maximum  maximum_cons eval_add eval_max)
open ThreeBoundRankNumeric ThreeBoundFullProfile









theorem get_zeroHits (h : Fin 3) : zeroHits.get h=0 := by
  fin_cases h <;> rfl

theorem get_maxHits (a b : HitValues) (h : Fin 3) :
    (maxHits a b).get h=max (a.get h) (b.get h) := by
  fin_cases h <;> rfl



theorem stateHits_get (n : ℕ) (v : Profile n) (a c : Entry) (k : Fin 11)
    (x y : ℕ) (h : Fin 3) :
    (stateHits n v a c k x y).get h=(stateCost n a c k x y h.val).eval v := by
  fin_cases h <;> simp only [HitValues.get,stateHits,stateCost,Fin.val_zero,Fin.val_one,
    Fin.reduceFinMk,↓reduceIte,eval_add,eval_max,ThreeBoundMinmaxNumeric.eval_ite]



theorem get_foldr_maxHits (xs : List HitValues) (h : Fin 3) :
    (xs.foldr maxHits zeroHits).get h=maximum (xs.map fun value => value.get h) := by
  induction xs with
  | nil => exact get_zeroHits h
  | cons value xs ih =>
      simpa only [List.foldr_cons,List.map_cons,maximum_cons,get_maxHits,ih]

theorem fusedHits_get (n : ℕ) (v : Profile n) (a c : Entry) (k : Fin 11) (h : Fin 3) :
    (fusedHits n v a c k).get h=(rankCost n a c k h.val).eval v := by
  rw [fusedHits,get_foldr_maxHits,rankCost,Expr.eval_maximum]
  apply congrArg maximum
  simp only [List.map_flatMap]
  apply congrArg (fun f => (List.range n).flatMap f)
  funext x
  rw [List.map_filterMap,List.map_filterMap]
  apply congrArg (fun f => (List.range n).filterMap f)
  funext y
  by_cases hp : Possible a c k x y
  · simp only [if_pos hp,Option.map_some,stateHits_get]
  · simp only [if_neg hp,Option.map_none]

theorem rankCost_zero_of_possible_false (n : ℕ) (a c : Entry) (k : Fin 11)
    (hp : possible n a c k=false) (h : ℕ) : rankCost n a c k h=Expr.zero := by
  have hno : ∀ x∈List.range n, ∀ y∈List.range n, ¬Possible a c k x y := by
    intro x hx y hy hxy
    have hh : possible n a c k=true := by
      apply List.any_eq_true.mpr
      refine ⟨x,hx,?_⟩
      apply List.any_eq_true.mpr
      exact ⟨y,hy,decide_eq_true hxy⟩
    rw [hp] at hh
    contradiction
  have hempty : ((List.range n).flatMap fun x => (List.range n).filterMap fun y =>
      if Possible a c k x y then some (stateCost n a c k x y h) else none)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro x hx
    apply List.filterMap_eq_nil_iff.mpr
    intro y hy
    exact if_neg (hno x hx y hy)
  simp only [rankCost,hempty,Expr.maximum,List.foldr_nil]



theorem storedHits_get (values : CostValues) (k : Fin 11) (h : Fin 3) :
    (storedHits values k).get h=values.heads.getD (3*k.val+h.val) 0 := by
  fin_cases h <;> rfl









theorem fusedCoeffCheck_sound (n : ℕ) (v : Profile n) (a c : Entry) (mask : Array Bool)
    (hm : MaskOK n a c mask) (values : CostValues)
    (hc : fusedCoeffCheck n v a c mask values=true) : CostOK n v a c values := by
  have hh : fusedHeadCheck n v a c mask values=true ∧ decide (TailOK n v a c values)=true := by
    simpa only [fusedCoeffCheck,Bool.and_eq_true] using hc
  refine ⟨?_,of_decide_eq_true hh.2⟩
  intro k h
  have hk := List.all_eq_true.mp hh.1 k (List.mem_finRange k)
  change (if mask.getD k.val false then decide (storedHits values k=fusedHits n v a c k)
    else decide (storedHits values k=zeroHits))=true at hk
  by_cases hmask : mask.getD k.val false=true
  · rw [if_pos hmask] at hk
    have he := congrArg (fun vv : HitValues => vv.get h) (of_decide_eq_true hk)
    simpa only [storedHits_get,fusedHits_get] using he
  · rw [if_neg hmask] at hk
    have hfalse : possible n a c k=false := by
      rw [← hm k]
      exact Bool.eq_false_iff.mpr hmask
    have he := congrArg (fun vv : HitValues => vv.get h) (of_decide_eq_true hk)
    rw [rankCost_zero_of_possible_false n a c k hfalse h.val]
    simpa only [storedHits_get,get_zeroHits,Expr.eval] using he

end ThreeBoundRankCached



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (n : Nat) (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (a c : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry) (mask : Array.{0} Bool)
  (hm : Sensitivity213981Formal.ThreeBoundRankCached.MaskOK n a c mask)
  (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues)
  (hc : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankCached.fusedCoeffCheck n v a c mask values) Bool.true),
  Sensitivity213981Formal.ThreeBoundRankCached.CostOK n v a c values := @Sensitivity213981Formal.ThreeBoundRankCached.fusedCoeffCheck_sound
