-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxHybrid.coreBounds_scale
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:31.073103+00:00
-- url     : https://prove2.me/submissions/d02b5bf9-4db2-4d17-af68-74cf54b3fbd6

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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


namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile





theorem Expr.eval_homogeneous {n : ℕ} (e : Expr n) (v : Profile n) (c : ℕ) :
    e.eval (fun i => c * v i) = c * e.eval v := by
  induction e with
  | zero => simp [eval]
  | var i => rfl
  | add a b ha hb => simp only [eval, ha, hb, Nat.mul_add]
  | scale k a ha => simp only [eval, ha]; ring
  | sub a b ha hb => simp only [eval, ha, hb, Nat.mul_sub_left_distrib]
  | min a b ha hb => simp only [eval, ha, hb, Nat.mul_min_mul_left]
  | max a b ha hb => simp only [eval, ha, hb, Nat.mul_max_mul_left]




































end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Strict positive and union bounds with an independently verified scalar first bound. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem pCore_homogeneous (n pcross : ℕ) (v : Profile n) (j k l : Entry) (first c : ℕ) :
    pCore n pcross (scale c v) j k l (c*first)=c*pCore n pcross v j k l first := by
  have he (e : Expr n) : e.eval (scale c v)=c*e.eval v := Expr.eval_homogeneous e v c
  dsimp only [pCore]
  split_ifs <;> simp only [he,Nat.mul_left_comm pcross c,Nat.mul_left_comm 2 c,
    ← Nat.mul_add,Nat.mul_max_mul_left,Nat.mul_min_mul_left,Nat.mul_zero,
    Nat.max_zero,Nat.zero_max,Nat.min_zero,Nat.zero_min]

theorem dCore_homogeneous (n degree : ℕ) (v : Profile n) (i j k l : Entry) (first c : ℕ) :
    dCore n degree (scale c v) i j k l (c*first)=c*dCore n degree v i j k l first := by
  have he (e : Expr n) : e.eval (scale c v)=c*e.eval v := Expr.eval_homogeneous e v c
  dsimp only [dCore]
  split_ifs <;> simp only [he,Nat.mul_left_comm degree c,Nat.mul_left_comm (degree-1) c,
    ← Nat.mul_add,Nat.mul_max_mul_left,Nat.mul_min_mul_left,Nat.mul_zero,
    Nat.max_zero,Nat.zero_max,Nat.min_zero,Nat.zero_min]






end
end ThreeBoundMinmaxNumeric




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







theorem coreBounds_scale (degree pcross : ℕ) (recipe : Fin n → ThreeBoundMinmaxNumeric.Entry)
    (v w : Profile n) (h : CoreBounds degree pcross recipe v w) (c : ℕ) :
    CoreBounds degree pcross recipe (scale c v) (scale c w) := by
  have he (e : Expr n) : e.eval (scale c v)=c*e.eval v := Expr.eval_homogeneous e v c
  constructor
  · intro i j hij
    change (fullBExpr n degree (recipe i) (recipe j)).eval (scale c v) ≤  c*w (.b i j)
    rw [he]
    exact Nat.mul_le_mul_left c (h.b i j hij)
  · intro i j hij hjn
    change (fullMExpr n degree (recipe i) (recipe j) (recipe (next j))).eval (scale c v) ≤  c*w (.m i j)
    rw [he]
    exact Nat.mul_le_mul_left c (h.m i j hij hjn)
  · intro j l hjl
    change pCore n pcross (scale c v) (recipe j) (recipe (next j)) (recipe l)
      (c*w (.a (next j) l)) ≤  c*w (.p j l)
    rw [ThreeBoundMinmaxNumeric.pCore_homogeneous]
    exact Nat.mul_le_mul_left c (h.p j l hjl)
  · intro i j l hij hjl
    change dCore n degree (scale c v) (recipe i) (recipe j) (recipe (next j)) (recipe l)
      (c*w (.m i j)+c*w (.p j l)) ≤  c*w (.d i j l)
    rw [← Nat.mul_add,ThreeBoundMinmaxNumeric.dCore_homogeneous]
    exact Nat.mul_le_mul_left c (h.d i j l hij hjl)



end
end ThreeBoundMinmaxHybrid




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} (degree pcross : Nat) (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry)
  (v w : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (h : @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.CoreBounds n degree pcross recipe v w) (c : Nat),
  @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.CoreBounds n degree pcross recipe
    (@Sensitivity213981Formal.ThreeBoundFullProfile.scale n c v)
    (@Sensitivity213981Formal.ThreeBoundFullProfile.scale n c w) := @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.coreBounds_scale
