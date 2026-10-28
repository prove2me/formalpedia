-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.pCore_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:57.642877+00:00
-- url     : https://prove2.me/submissions/fec6389f-b432-4add-97cf-ae88a63e4682

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditionalNumeric_parent_eq_ordinary_valid
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictP_basic
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictP_refined
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_matched_same_parent
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_minusExpr_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_unionExpr_bound


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

theorem unionExpr_bound_all (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (i j k l : Fin n) (hij : i ≤  j) (hkl : k ≤  l) :
    DBound F i j k l ((unionExpr n i.val j.val k.val l.val).eval v) := by
  by_cases hjk : j <  k
  · exact unionExpr_bound F v hv i j k l hij hjk hkl
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



theorem plain_spec (e : Entry) (he : e.plain=true) (d : ℕ) (hd : d ≤  e.tolerance) :
    e.lowerAt d=e.upperAt d := by
  exact beq_iff_eq.mp (List.all_eq_true.mp he d (List.mem_range.mpr (by omega)))

theorem ordinary_spec (e : Entry) (he : e.ordinary=true) (d : ℕ) (hd : d ≤  e.tolerance) :
    e.lowerAt d=e.lowerAt 0 ∧ e.upperAt d=e.lowerAt 0 := by
  have hh := List.all_eq_true.mp he d (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true,beq_iff_eq] using hh

theorem ordinary_of_zero_plain (e : Entry) (hq : e.tolerance=0) (he : e.plain=true) :
    e.ordinary=true := by
  apply List.all_eq_true.mpr
  intro d hd
  have hd0 : d=0 := by have hh := List.mem_range.mp hd; omega
  subst d
  simp only [beq_self_eq_true,Bool.true_and,beq_iff_eq]
  exact (plain_spec e he 0 (Nat.zero_le _)).symm



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



theorem eval_ite {m : ℕ} (v : Profile m) (p : Prop) [Decidable p] (a b : Expr m) :
    (if p then a else b).eval v=if p then a.eval v else b.eval v := by
  split_ifs <;> rfl

end
end ThreeBoundMinmaxNumeric




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





theorem pCore_bound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (j k l : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F j k) (Q : ThreeBoundMinmaxTransfer.PairData S F k l)
    (hm : EntryMatch S F j k P (recipe j) (recipe k))
    (hn : EntryMatch S F k l Q (recipe k) (recipe l))
    (pcross first : ℕ)
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (pcross+1))
    (v : Profile n) (hv : Upper F v)
    (hA : ABound (parent S F) k l first) :
    PBound (parent S F) j k l (pCore n pcross v (recipe j) (recipe k) (recipe l) first) := by
  intro x hxj hxk
  have hfirst := hA x hxk
  dsimp only [pCore]
  by_cases hs : (recipe j).same (recipe k)=true
  · rw [if_pos hs]
    have he := matched_same_parent S F j k P (recipe j) (recipe k) hm hs
    rw [he,hxk] at hxj
    contradiction
  · rw [if_neg hs]
    by_cases hz : (recipe j).tolerance=0 ∧ (recipe l).tolerance=0 ∧
        (recipe j).plain=true ∧ (recipe k).plain=true ∧ (recipe l).plain=true
    · rw [if_pos hz]
      have hjq : S.tolerance j=0 := hm.weakTolerance.trans hz.1
      have hlq : S.tolerance l=0 := hn.strongTolerance.trans hz.2.1
      have hkq : S.tolerance k=0 := Nat.eq_zero_of_le_zero (by simpa only [hjq] using P.tolerances)
      have hkq' : (recipe k).tolerance=0 := hm.strongTolerance.symm.trans hkq
      have hjParent := matched_ordinary_weak S F j k P (recipe j) (recipe k) hm
        (ordinary_of_zero_plain _ hz.1 hz.2.2.1)
      have hkParent := matched_ordinary_strong S F j k P (recipe j) (recipe k) hm
        (ordinary_of_zero_plain _ hkq' hz.2.2.2.1)
      have hlParent := matched_ordinary_strong S F k l Q (recipe k) (recipe l) hn
        (ordinary_of_zero_plain _ hz.2.1 hz.2.2.2.2)
      rw [hjq] at hjParent
      rw [hkq] at hkParent
      rw [hlq] at hlParent
      rw [hjParent] at hxj
      rw [hkParent] at hxk
      have htjk : P.weakLower 0 ≤  P.strongLower 0 := P.lowerOrder 0 (Nat.zero_le _)
      have htkl : P.strongLower 0 ≤  Q.strongLower 0 := by
        rw [matched_middle_lower S F recipe j k l P Q hm hn 0 (Nat.zero_le _)]
        exact Q.lowerOrder 0 (Nat.zero_le _)
      have hgjtl : S.guard j ≤  Q.strongLower 0 :=
        (P.weakGuardTarget 0 (Nat.zero_le _)).trans (htjk.trans htkl)
      have hgltj : S.guard l ≤  P.weakLower 0 :=
        (Q.guards.trans P.guards).trans (P.weakGuardTarget 0 (Nat.zero_le _))
      have hgltl : S.guard l ≤  Q.strongLower 0 := Q.guardTarget 0 (Nat.zero_le _)
      have ha := aExpr_bound F v hv (S.guard j) (Q.strongLower 0) hgjtl
      have hb := bExpr_bound F v hv (S.guard l) (P.weakLower 0) hgltj
      have hp := plusExpr_bound_all F hF v hv (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) htkl
      have hmg := minusExpr_bound_all F hF v hv (S.guard l) (S.guard k) (S.guard j) Q.guards
      have hbk := bExpr_bound F v hv (S.guard l) (P.strongLower 0) (hgltj.trans htjk)
      have hbl := bExpr_bound F v hv (S.guard l) (Q.strongLower 0) hgltl
      have hmt := minusExpr_bound_all F hF v hv (S.guard l) (P.weakLower 0) (P.strongLower 0) hgltj
      have hu := unionExpr_bound_all F hF v hv (S.guard l) (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) hgltj htkl
      have hbasic := strictP_basic S hT F hF (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0)
        (S.guard j) (S.guard k) (S.guard l) htkl Q.guards hgjtl hgltj hgltl
        pcross _ _ _ _ hcap hb ha hp hmg x hxj hxk
      have hrefined := strictP_refined S hT F hF (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0)
        (S.guard j) (S.guard k) (S.guard l) htjk htkl P.guards Q.guards hgjtl hgltj hgltl
        pcross _ _ _ _ _ _ hcap ha hmt hbk hbl hu hmg x hxj hxk
      refine le_min (le_min hfirst ?_) ?_
      · rw [hlParent]
        simpa only [eval_add,eval_mul,eval_max,hm.weakGuard,hm.strongGuard,hn.strongGuard,
          hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),hn.strongLower 0 (Nat.zero_le _)] using hbasic
      · rw [hlParent]
        simpa only [eval_add,eval_mul,eval_max,eval_zero,eval_ite,Fin.lt_def,
          hm.weakGuard,hm.strongGuard,hn.strongGuard,
          hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),hn.strongLower 0 (Nat.zero_le _)] using hrefined
    · rw [if_neg hz]
      exact hfirst




end
end ThreeBoundMinmaxNumeric




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
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry) (j k l : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F j k)
  (Q :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F k l)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F j k P (recipe j) (recipe k))
  (hn : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F k l Q (recipe k) (recipe l))
  (pcross first : Nat)
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pcross
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hA :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
      (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) k l first),
  @Sensitivity213981Formal.ThreeBoundProfiles.PBound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) j k l
    (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.pCore n pcross v (recipe j) (recipe k) (recipe l) first) := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.pCore_bound
