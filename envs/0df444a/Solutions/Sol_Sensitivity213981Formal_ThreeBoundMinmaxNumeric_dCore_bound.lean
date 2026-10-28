-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.dCore_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:58.284098+00:00
-- url     : https://prove2.me/submissions/e6df8b9d-617d-411d-bc59-4a0ad7a01b4f

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_matched_same_parent
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_strictD_parent
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







theorem matched_middle_lower (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (recipe : Fin n → Entry) (i j k : Fin n)
    (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k)) (d : ℕ) (hd : d ≤  S.tolerance j) :
    P.strongLower d=Q.weakLower d := Fin.ext ((hm.strongLower d hd).trans (hn.weakLower d hd).symm)

theorem matched_middle_upper (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (recipe : Fin n → Entry) (i j k : Fin n)
    (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k)) (d : ℕ) (hd : d ≤  S.tolerance j) :
    P.strongUpper d=Q.weakUpper d := Fin.ext ((hm.strongUpper d hd).trans (hn.weakUpper d hd).symm)







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








theorem dCore_bound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k l : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (Q : ThreeBoundMinmaxTransfer.PairData S F j k) (R : ThreeBoundMinmaxTransfer.PairData S F k l)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (ho : EntryMatch S F k l R (recipe k) (recipe l))
    (degree first : ℕ)
    (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v)
    (hD : DBound (parent S F) i j k l first) :
    DBound (parent S F) i j k l
      (dCore n degree v (recipe i) (recipe j) (recipe k) (recipe l) first) := by
  classical
  intro x hxj hxk
  have hfirst := hD x hxj hxk
  dsimp only [dCore]
  by_cases hs : (recipe j).same (recipe k)=true
  · rw [if_pos hs]
    have he := matched_same_parent S F j k Q (recipe j) (recipe k) hn hs
    rw [he,hxk] at hxj
    contradiction
  · rw [if_neg hs]
    by_cases hz : (recipe j).tolerance=0 ∧ (recipe l).tolerance=0 ∧
        (recipe l).plain=true ∧ (recipe k).upperAt 0 ≤  (recipe l).lowerAt 0
    · rw [if_pos hz]
      refine le_min ?_ ?_
      · exact hfirst
      · have hjq : S.tolerance j=0 := hm.strongTolerance.trans hz.1
        have hlq : S.tolerance l=0 := ho.strongTolerance.trans hz.2.1
        have hlplain : R.strongUpper 0=R.strongLower 0 := by
          apply Fin.ext
          rw [ho.strongUpper 0 (Nat.zero_le _),ho.strongLower 0 (Nat.zero_le _)]
          exact (plain_spec (recipe l) hz.2.2.1 0 (Nat.zero_le _)).symm
        have hldef : ∀ u z, S.target l 0 u z=mm F (R.strongLower 0) (R.strongLower 0) u z := by
          intro u z
          rw [R.strongDef,hlplain]
        have htjk : P.strongLower 0 ≤  Q.strongLower 0 := by
          rw [matched_middle_lower S F recipe i j k P Q hm hn 0 (Nat.zero_le _)]
          exact Q.lowerOrder 0 (Nat.zero_le _)
        have hujk : P.strongUpper 0 ≤  Q.strongUpper 0 := by
          rw [matched_middle_upper S F recipe i j k P Q hm hn 0 (Nat.zero_le _)]
          exact Q.upperOrder 0 (Nat.zero_le _)
        have hukl : Q.strongUpper 0 ≤  R.strongLower 0 := by
          change (Q.strongUpper 0).val ≤  (R.strongLower 0).val
          rw [hn.strongUpper 0 (Nat.zero_le _),ho.strongLower 0 (Nat.zero_le _)]
          exact hz.2.2.2
        have htkl := (Q.strongLowerUpper 0 (Nat.zero_le _)).trans hukl
        have htij := P.lowerOrder 0 (Nat.zero_le _)
        have huij := P.upperOrder 0 (Nat.zero_le _)
        have haM := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
        have hm0 := minusExpr_bound_all F hF v hv (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) htij
        have hm1 := minusExpr_bound_all F hF v hv (P.weakUpper 0) (P.strongUpper 0) (Q.strongUpper 0) huij
        have hbm0 := bExpr_bound F v hv (P.weakLower 0) (Q.strongLower 0) (htij.trans htjk)
        have hbm1 := bExpr_bound F v hv (P.weakUpper 0) (Q.strongUpper 0) (huij.trans hujk)
        have hp := plusExpr_bound_all F hF v hv (S.guard k) (S.guard j) (S.guard i) P.guards
        have hb0 := bExpr_bound F v hv (P.weakLower 0) (R.strongLower 0) (htij.trans (htjk.trans htkl))
        have hb1 := bExpr_bound F v hv (P.weakUpper 0) (R.strongLower 0) (huij.trans (hujk.trans hukl))
        have haD := aExpr_bound F v hv (S.guard l) (S.guard i) (R.guards.trans (Q.guards.trans P.guards))
        have hdt := unionExpr_bound_all F hF v hv (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) (R.strongLower 0) htij htkl
        have hdg := unionExpr_bound_all F hF v hv (S.guard l) (S.guard k) (S.guard j) (S.guard i) R.guards P.guards
        have hh := minmax_strictD_parent S hT F hF i j k l P Q hjq hlq (R.strongLower 0) hldef
          (hujk.trans hukl) hukl R.guards degree _ _ _ _ _ _ _ _ _ _ _ hd
          haM hm0 hm1 hbm0 hbm1 hp hb0 hb1 haD hdt hdg x hxj hxk
        simpa only [pairMExpr,pairMCost,pairMTarget,eval_add,eval_mul,eval_max,eval_zero,eval_ite,Fin.lt_def,
          hm.weakLower 0 (Nat.zero_le _),hm.weakUpper 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),hm.strongUpper 0 (Nat.zero_le _),
          hn.strongLower 0 (Nat.zero_le _),hn.strongUpper 0 (Nat.zero_le _),ho.strongLower 0 (Nat.zero_le _),
          hm.weakGuard,hm.strongGuard,hn.strongGuard,ho.strongGuard] using hh
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
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry) (i j k l : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (Q :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F j k)
  (R :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F k l)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P (recipe i) (recipe j))
  (hn : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F j k Q (recipe j) (recipe k))
  (ho : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F k l R (recipe k) (recipe l))
  (degree first : Nat)
  (hd :
    ∀ (w : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing (Fin n) I V inst_1 S w))
        degree)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hD :
    @Sensitivity213981Formal.ThreeBoundProfiles.DBound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
      (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) i j k l first),
  @Sensitivity213981Formal.ThreeBoundProfiles.DBound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) i j k l
    (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.dCore n degree v (recipe i) (recipe j) (recipe k) (recipe l) first) := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.dCore_bound
