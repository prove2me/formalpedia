-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxRank.rankMTerm_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:36:40.80912+00:00
-- url     : https://prove2.me/submissions/ce4270d6-ce1b-4f87-8f71-a6e37f24c5ae

import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_MinmaxRankData
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_rejected_capacity_le_count
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_row_capacity_data
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_target_rank_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_capacity_M_row


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























end
end ThreeBoundHeadExpressions






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











end
end ThreeBoundMinmaxTransfer




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











theorem failed_card_le_outgoing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (failed S F j x v).card ≤  (outgoing S v).card := by
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.1⟩





end
end ThreeBoundMinmaxTransfer





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact-rank conditional M expression for actual min/max parents. -/


set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxRank
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundConditional
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rankMTerm_bound (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (hF : Nested F) (i j k : Fin n) (P : PairData S F i j) (Q : PairData S F j k) (a c e : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (hn : ThreeBoundMinmaxNumeric.EntryMatch S F j k Q c e)
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (hcount : (failed S F j x w).card≤ S.tolerance j)
    (hstrong : mm F (P.strongLower (failed S F j x w).card) (P.strongUpper (failed S F j x w).card)
      (child x w false) (child x w true)=true) (hxk : parent S F k x=false) :
    (flipsTo (parent S F i) false x).card≤ (rankMTerm n degree a c e rx.val ry.val).eval v := by
  have hdata := row_capacity_data S F hF i j P a c hm x w side rx ry hx hy hxy hcount hstrong
  let da := capacityHeight a rx.val ry.val-1
  let db := capacityHeight c rx.val ry.val-1
  let gap := capacityHeight e rx.val ry.val-db
  have hdbi : db≤ S.tolerance i := hdata.strong_tolerance.trans P.tolerances
  have hweakdb := mm_mono F hF _ _ _ _ (P.lowerOrder db hdata.strong_tolerance)
    (P.upperOrder db hdata.strong_tolerance) _ _ hdata.strong_target
  have htarget := target_rank_bound F hF v hv a db (P.weakLower db) (P.weakUpper db)
    (P.weakLowerUpper db hdbi) (hm.weakLower db hdbi) (hm.weakUpper db hdbi)
    x w side rx ry hx hy hxy hweakdb
  have hnext := rejected_capacity_le_count S F hF j k Q c e hn x w side rx ry hx hy hxy hxk
  have hnextdegree : capacityHeight e rx.val ry.val≤ degree :=
    hnext.trans ((failed_card_le_outgoing S F k x w).trans (hd w).le)
  have hgap : gap≤ (guardFailures S F (S.guard k) x w).card-(failed S F j x w).card := by
    change gap≤ (failed S F k x w).card-(failed S F j x w).card
    dsimp [gap,db]
    have hc := hdata.guard_count
    omega
  have hnotSame : ¬(e.guard=c.guard ∧ 0< gap) := by
    rintro ⟨he,hg⟩
    have hguard : S.guard k=S.guard j := Fin.ext (hn.strongGuard.trans (he.trans hn.weakGuard.symm))
    have hfail : failed S F k x w=failed S F j x w := by simp only [failed,hguard]
    rw [hfail] at hnext
    have hc := hdata.guard_count
    dsimp [gap,db] at hg
    omega
  have hgapDegree : gap≤ degree-db := Nat.sub_le_sub_right hnextdegree db
  have hA := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hP := plusExpr_bound_all F hF v hv (S.guard k) (S.guard j) (S.guard i) P.guards
  have hh := minmax_capacity_M_row S F hF i j P (S.guard k) Q.guards x w da db degree _ gap _ _
    hdata.guard_count hdata.strong_tolerance hdata.strong_target hdata.weak_tolerance hdata.capacity_order
    hdata.weak_target (hd w) htarget hgap hA hP
  have heq : (capacityHeight a rx.val ry.val=capacityHeight c rx.val ry.val) ↔ da=db := by
    dsimp [da,db]
    have hpa := hdata.weak_pos
    have hpc := hdata.strong_pos
    omega
  have hne : capacityHeight c rx.val ry.val≠0 := Nat.ne_of_gt hdata.strong_pos
  have hneed := And.intro hdata.need_lower hdata.need_upper
  unfold rankMTerm
  rw [if_neg hne,if_neg (Nat.not_lt_of_ge hnextdegree),if_neg hnotSame,if_pos hneed]
  by_cases hgate : capacityHeight a rx.val ry.val=capacityHeight c rx.val ry.val ∧ db≤ degree
  · rw [if_pos hgate,if_neg (Nat.not_lt_of_ge hgapDegree)]
    have hgate' : da=db ∧ db≤ degree := ⟨heq.mp hgate.1,hgate.2⟩
    simpa only [if_pos hgate',eval_add,eval_mul,eval_min,hm.weakGuard,hm.strongGuard,hn.strongGuard,Nat.add_assoc] using hh
  · rw [if_neg hgate]
    have hgate' : ¬(da=db ∧ db≤ degree) := fun h => hgate ⟨heq.mpr h.1,h.2⟩
    simpa only [if_neg hgate',Nat.add_zero] using hh



end
end ThreeBoundMinmaxRank



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
  (i j k : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (Q :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F j k)
  (a c e : Sensitivity213981Formal.ThreeBoundMinmaxRank.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (hn : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F j k Q c e) (degree : Nat)
  (hd :
    ∀ (w : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing (Fin n) I V inst_1 S w))
        degree)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (side : Bool) (rx ry : Fin n)
  (hx :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not side)) rx)
  (hy :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w side) ry)
  (hxy : @LE.le.{0} (Fin n) (@instLEFin n) rx ry)
  (hcount :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst_1 S F j x w))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j))
  (hstrong :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P
          (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst_1 S F j x w)))
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P
          (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst_1 S F j x w)))
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.true))
      Bool.true)
  (hxk : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F k x) Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
        (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F i) Bool.false x))
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundMinmaxRank.rankMTerm n degree a c e (@Fin.val n rx) (@Fin.val n ry))) := @Sensitivity213981Formal.ThreeBoundMinmaxRank.rankMTerm_bound
