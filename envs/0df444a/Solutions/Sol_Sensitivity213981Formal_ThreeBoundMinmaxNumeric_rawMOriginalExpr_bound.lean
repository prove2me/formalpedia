-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.rawMOriginalExpr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:27:14.74322+00:00
-- url     : https://prove2.me/submissions/a0cd446a-1d45-4284-852f-ae0c5fdf8812

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_OrdinaryParentBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditionalNumeric_parent_eq_ordinary_valid
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_primitiveM
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_rawBExpr_bound
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







theorem mem_interval {a b k : ℕ} : k ∈ interval a b ↔ a ≤  k ∧ k <  b := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨k-a,by omega,by omega⟩











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
@[simp] theorem eval_min {n : ℕ} (v : Profile n) (a b : Expr n) :
    (min a b).eval v = min (a.eval v) (b.eval v) := rfl
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

theorem bool_boundary (f : ℕ → Bool) (j k : ℕ) (hjk : j <  k)
    (hj : f j = true) (hk : f k = false) :
    ∃ m, j ≤  m ∧ m <  k ∧ f m = true ∧ f (m+1) = false := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases hm : f k with
      | true => exact ⟨k,by omega,by omega,hm,hk⟩
      | false =>
          have hjk' : j <  k := by
            by_contra h
            have : j = k := by omega
            subst j
            simp [hm] at hj
          obtain ⟨m,hmj,hmk,hmt,hmf⟩ := ih hjk' hm
          exact ⟨m,hmj,by omega,hmt,hmf⟩

theorem fin_bool_boundary {n : ℕ} (f : Fin n → Bool) (j k : Fin n)
    (hjk : j <  k) (hj : f j = true) (hk : f k = false) :
    ∃ m : Fin n, j ≤  m ∧ m <  k ∧ f m = true ∧ f (next m) = false := by
  let ff : ℕ → Bool := fun a => if h : a <  n then f ⟨a,h⟩ else false
  have hj' : ff j.val = true := by simpa [ff] using hj
  have hk' : ff k.val = false := by simpa [ff] using hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := bool_boundary ff j.val k.val hjk hj' hk'
  have hmn : m <  n := hmk.trans k.isLt
  have hmn' : m+1 <  n := lt_of_le_of_lt hmk k.isLt
  refine ⟨⟨m,hmn⟩,hmj,hmk,?_,?_⟩
  · simpa [ff,hmn] using hmt
  · simpa [ff,hmn',next] using hmf

variable {n : ℕ} {I : Type} [Fintype I]

theorem aExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤  j) :
    ABound F i j ((aExpr n i.val j.val).eval v) := by
  simpa only [aExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.a i j) hij

theorem bExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤  j) :
    BBound F i j ((bExpr n i.val j.val).eval v) := by
  simpa only [bExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.b i j) hij



theorem plusExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k : Fin n) (hij : i <  j) (hjk : j ≤  k) :
    PBound F i j k ((plusExpr n i.val j.val k.val).eval v) := by
  intro x hi hj
  obtain ⟨m,hmi,hmj,hmt,hmf⟩ := fin_bool_boundary (fun t => F t x) i j hij hi hj
  have hm := hv (.p m k) (hmj.trans_le hjk) x hmt hmf
  apply hm.trans
  simp only [plusExpr, if_pos (show i.val <  j.val ∧ j.val ≤  k.val from ⟨hij,hjk⟩),
    Expr.eval_maximum, List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨m.val,mem_interval.mpr ⟨hmi,hmj⟩,?_⟩
  simp only [Function.comp_apply,pExpr,dif_pos m.isLt,dif_pos k.isLt,Expr.eval]



end ThreeBoundNumeric





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









@[simp] theorem ordinary_failed (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g l : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (ordinaryStage S F t g q) F l x v = guardFailures S F g x v := rfl

@[simp] theorem ordinary_parent_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent_true_iff, ordinary_failed, ordinaryStage,
    Bool.and_eq_true, ordinaryRow]
  constructor
  · rintro ⟨v,hc,hf,ht⟩
    exact ⟨v, fun c => by cases c <;> assumption, hc⟩
  · rintro ⟨v,ht,hc⟩
    exact ⟨v,hc,ht false,ht true⟩































































end
end ThreeBoundConditional




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

theorem plusExpr_bound_all (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (i j k : Fin n) (hjk : j ≤  k) :
    PBound F i j k ((plusExpr n i.val j.val k.val).eval v) := by
  by_cases hij : i <  j
  · exact plusExpr_bound F v hv i j k hij hjk
  · intro x hi hj
    have he := hF j i (le_of_not_gt hij) x hi
    rw [hj] at he
    contradiction

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
/- Semantic interpretation of numeric entries, ordinary components and raw B. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ThreeBoundConditionalNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]





















/-- Exact expression interpretation of the improved ordinary-component M bound. -/
theorem primitiveMExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ti tj tk gi gj gk : Fin n) (qi q : ℕ) (j k : Entry)
    (htj : tj.val=j.t0) (htk : tk.val=k.t0) (hgj : gj.val=j.guard) (hgk : gk.val=k.guard)
    (hjq : j.tolerance=q)
    (htij : ti ≤  tj) (htjk : tj ≤  tk) (hgjgi : gj ≤  gi) (hgkgj : gk ≤  gj) (hq : q ≤  qi)
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj q x=true) (hxk : ordinaryParent S F tk gk q x=false) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤ 
      (primitiveMExpr n degree ti.val gi.val qi j k).eval v := by
  have hm := minusExpr_bound_all F hF v hv ti tj tk htij
  have hb := bExpr_bound F v hv ti tk (htij.trans htjk)
  have ha := aExpr_bound F v hv gj gi hgjgi
  have hp := plusExpr_bound_all F hF v hv gk gj gi hgjgi
  have hh := primitiveM S F hF ti tj tk gi gj gk htij htjk hgjgi hgkgj qi q hq
    degree _ _ _ _ hd hm hb ha hp x hxj hxk
  simpa only [primitiveMExpr,← htj,← htk,← hgj,← hgk,hjq,
    eval_max,eval_add,eval_mul,eval_zero,Fin.lt_def,apply_ite] using hh

end
end ThreeBoundConditionalNumeric




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



theorem mm_mono (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj : L) (ht : ti ≤  tj) (hu : ui ≤  uj) (x y : I → Bool)
    (h : mm F tj uj x y=true) : mm F ti ui x y=true := by
  rw [mm_true] at h ⊢
  exact ⟨hF _ _ ht _ h.1,hF _ _ ht _ h.2.1,
    h.2.2.elim (fun hh => Or.inl (hF _ _ hu _ hh)) (fun hh => Or.inr (hF _ _ hu _ hh))⟩



theorem parent_true_of_count (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hd : d ≤  S.tolerance l) (hc : (failed S F l x w).card ≤  d)
    (hm : mm F (t d) (u d) (child x w false) (child x w true)=true) : parent S F l x=true := by
  apply (parent_true_iff S F l x).2
  refine ⟨w,hc.trans hd,?_⟩
  rw [hdef]
  exact mm_mono F hF _ _ _ _ (ht hc) (hu hc) _ _ hm





/-- Fixing which child supplies the upper threshold gives an actual component
of the symmetric parent at every safe upper bound on the failed-guard count. -/
theorem oriented_component_accepts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤  S.tolerance l → t b ≤  u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ) (c : Bool)
    (hd : d ≤  S.tolerance l) (hc : (failed S F l x w).card ≤  d)
    (hlow : F (t d) (child x w (!c))=true) (hhigh : F (u d) (child x w c)=true) :
    parent S F l x=true := by
  apply parent_true_of_count S F hF l t u ht hu hdef x w d hd hc
  have hlow' := hF _ _ (hlu d hd) _ hhigh
  cases c <;> simp_all only [Bool.not_false,Bool.not_true,mm_true,true_or,or_true,and_self]

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









theorem oriented_implies_parent (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤  S.tolerance l → t b ≤  u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ) (c : Bool) (hd : d ≤  S.tolerance l)
    (hrow : orientedRow S F (t d) (u d) (S.guard l) d x w c) : parent S F l x=true :=
  oriented_component_accepts S F hF l t u ht hu hlu hdef x w d c hd hrow.2.2 hrow.1 hrow.2.1















end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The strict oriented-union estimate for actual graded min/max parents. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_same (F : L → (I → Bool) → Bool) (t : L) (x y : I → Bool) :
    mm F t t x y=(F t x && F t y) := by
  cases hx : F t x <;> cases hy : F t y <;> simp [mm,hx,hy]





end
end ThreeBoundMinmaxTransfer



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Constant upper-threshold components of actual graded min/max parents. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundConditionalNumeric ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem ordinary_upper_component_accepts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤  S.tolerance l → t b ≤  u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (d : ℕ) (hd : d ≤  S.tolerance l) (x : ((V × Bool) × I) → Bool)
    (hx : ordinaryParent S F (u d) (S.guard l) d x=true) : parent S F l x=true := by
  obtain ⟨w,htarget,hcount⟩ := (ordinary_parent_true S F (u d) (S.guard l) d x).1 hx
  exact oriented_implies_parent S F hF l t u ht hu hlu hdef x w d false hd
    ⟨hF _ _ (hlu d hd) _ (htarget true),htarget false,hcount⟩

theorem ordinary_upper_component_down_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤  S.tolerance l → t b ≤  u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (d : ℕ) (hd : d ≤  S.tolerance l) (x : ((V × Bool) × I) → Bool) :
    flipsTo (parent S F l) false x ⊆ flipsTo (ordinaryParent S F (u d) (S.guard l) d) false x := by
  intro bit hbit
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  cases hh : ordinaryParent S F (u d) (S.guard l) d (_root_.OAI.Paper320.flip x {bit}) with
  | false => rfl
  | true =>
    have hon := ordinary_upper_component_accepts S F hF l t u ht hu hlu hdef d hd _ hh
    rw [(Finset.mem_filter.mp hbit).2] at hon
    contradiction

variable {n : ℕ}



end
end ThreeBoundMinmaxTransfer




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





theorem ordinary_spec (e : Entry) (he : e.ordinary=true) (d : ℕ) (hd : d ≤  e.tolerance) :
    e.lowerAt d=e.lowerAt 0 ∧ e.upperAt d=e.lowerAt 0 := by
  have hh := List.all_eq_true.mp he d (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true,beq_iff_eq] using hh





theorem matched_middle_lower (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (recipe : Fin n → Entry) (i j k : Fin n)
    (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k)) (d : ℕ) (hd : d ≤  S.tolerance j) :
    P.strongLower d=Q.weakLower d := Fin.ext ((hm.strongLower d hd).trans (hn.weakLower d hd).symm)



theorem matched_ordinary_weak (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (ha : a.ordinary=true) :
    parent S F i=ordinaryParent S F (P.weakLower 0) (S.guard i) (S.tolerance i) := by
  apply ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
  intro d hd u z
  obtain ⟨hl,hu⟩ := ordinary_spec a ha d (by simpa only [hm.weakTolerance] using hd)
  have hl' : P.weakLower d=P.weakLower 0 := Fin.ext (by rw [hm.weakLower d hd,hm.weakLower 0 (Nat.zero_le _)]; exact hl)
  have hu' : P.weakUpper d=P.weakLower 0 := Fin.ext (by rw [hm.weakUpper d hd,hm.weakLower 0 (Nat.zero_le _)]; exact hu)
  rw [P.weakDef,hl',hu',mm_same]

theorem matched_ordinary_strong (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (hc : c.ordinary=true) :
    parent S F j=ordinaryParent S F (P.strongLower 0) (S.guard j) (S.tolerance j) := by
  apply ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
  intro d hd u z
  obtain ⟨hl,hu⟩ := ordinary_spec c hc d (by simpa only [hm.strongTolerance] using hd)
  have hl' : P.strongLower d=P.strongLower 0 := Fin.ext (by rw [hm.strongLower d hd,hm.strongLower 0 (Nat.zero_le _)]; exact hl)
  have hu' : P.strongUpper d=P.strongLower 0 := Fin.ext (by rw [hm.strongUpper d hd,hm.strongLower 0 (Nat.zero_le _)]; exact hu)
  rw [P.strongDef,hl',hu',mm_same]





end
end ThreeBoundMinmaxNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact min/max raw-M expression semantics. -/


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

theorem rawMOriginalExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v) :
    MBound (parent S F) i j k ((rawMOriginalExpr n degree (recipe i) (recipe j) (recipe k)).eval v) := by
  intro x hxj hxk
  have hb := rawBExpr_bound S F hF recipe i j P hm degree hd v hv x hxj
  dsimp only [rawMOriginalExpr]
  by_cases hbad : (Bool.not (recipe j).ordinary = true) ∨ (Bool.not (recipe k).ordinary = true) ∨
      (recipe j).tolerance ≠ (recipe k).tolerance
  · rw [if_pos hbad]
    exact hb
  · rw [if_neg hbad]
    have hjOrd : (recipe j).ordinary=true := by
      cases he : (recipe j).ordinary with
      | false => exact False.elim (hbad (Or.inl (by simp [he])))
      | true => rfl
    have hkOrd : (recipe k).ordinary=true := by
      cases he : (recipe k).ordinary with
      | false => exact False.elim (hbad (Or.inr (Or.inl (by simp [he]))))
      | true => rfl
    have heq : (recipe j).tolerance=(recipe k).tolerance := by
      by_contra he
      exact hbad (Or.inr (Or.inr he))
    have hq : S.tolerance j=S.tolerance k := by rw [hn.weakTolerance,hn.strongTolerance,heq]
    have hjParent := matched_ordinary_weak S F j k Q (recipe j) (recipe k) hn hjOrd
    have hkParent := matched_ordinary_strong S F j k Q (recipe j) (recipe k) hn hkOrd
    rw [hjParent] at hxj
    rw [hkParent,← hq] at hxk
    by_cases hi : (recipe i).ordinary=true
    · rw [if_pos hi]
      have hiParent := matched_ordinary_weak S F i j P (recipe i) (recipe j) hm hi
      have htij : P.weakLower 0 ≤  Q.weakLower 0 := by
        rw [← matched_middle_lower S F recipe i j k P Q hm hn 0 (Nat.zero_le _)]
        exact P.lowerOrder 0 (Nat.zero_le _)
      have hh := ThreeBoundConditionalNumeric.primitiveMExpr_bound S F hF
        (P.weakLower 0) (Q.weakLower 0) (Q.strongLower 0)
        (S.guard i) (S.guard j) (S.guard k) (S.tolerance i) (S.tolerance j)
        (recipe j).base (recipe k).base
        (hn.weakLower 0 (Nat.zero_le _)) (hn.strongLower 0 (Nat.zero_le _))
        hn.weakGuard hn.strongGuard hn.weakTolerance.symm
        htij (Q.lowerOrder 0 (Nat.zero_le _)) P.guards Q.guards P.tolerances degree hd v hv x hxj hxk
      rw [hiParent]
      simpa only [primitiveMExpr,hm.weakLower 0 (Nat.zero_le _),hm.weakGuard,hm.weakTolerance] using hh
    · rw [if_neg hi,eval_min]
      refine le_min hb ?_
      have htop : P.strongUpper (S.tolerance j)=Q.weakLower 0 := by
        apply Fin.ext
        rw [hm.strongUpper _ le_rfl,hn.weakLower 0 (Nat.zero_le _)]
        exact (ordinary_spec (recipe j) hjOrd _ (by rw [← hm.strongTolerance])).2
      have htij : P.weakUpper (S.tolerance j) ≤  Q.weakLower 0 := by
        rw [← htop]
        exact P.upperOrder _ le_rfl
      have hh := ThreeBoundConditionalNumeric.primitiveMExpr_bound S F hF
        (P.weakUpper (S.tolerance j)) (Q.weakLower 0) (Q.strongLower 0)
        (S.guard i) (S.guard j) (S.guard k) (S.tolerance j) (S.tolerance j)
        (recipe j).base (recipe k).base
        (hn.weakLower 0 (Nat.zero_le _)) (hn.strongLower 0 (Nat.zero_le _))
        hn.weakGuard hn.strongGuard hn.weakTolerance.symm
        htij (Q.lowerOrder 0 (Nat.zero_le _)) P.guards Q.guards le_rfl degree hd v hv x hxj hxk
      have hsub := ordinary_upper_component_down_subset S F hF i P.weakLower P.weakUpper
        P.weakLowerMono P.weakUpperMono P.weakLowerUpper P.weakDef (S.tolerance j) P.tolerances x
      have hc := (Finset.card_le_card hsub).trans hh
      rw [hm.weakUpper _ P.tolerances] at hc
      simpa only [primitiveMExpr,hm.weakGuard,hm.strongTolerance] using hc







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
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry) (i j k : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (Q :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F j k)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P (recipe i) (recipe j))
  (hn : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F j k Q (recipe j) (recipe k))
  (degree : Nat)
  (hd :
    ∀ (w : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing (Fin n) I V inst_1 S w))
        degree)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v),
  @Sensitivity213981Formal.ThreeBoundProfiles.MBound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) i j k
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.rawMOriginalExpr n degree (recipe i) (recipe j) (recipe k))) := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.rawMOriginalExpr_bound
