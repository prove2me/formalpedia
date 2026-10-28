-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinaryAExpr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:46:32.39834+00:00
-- url     : https://prove2.me/submissions/be1184ee-f4d4-4b3e-8aac-cf29ca6695b5

import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Numeric
import Definitions.Def_Sensitivity213981Formal_OrdinaryParentBridge
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_archive_eq
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinary5591_ordinary_positive_of_cases


namespace Sensitivity213981Formal
section
/- Exact compatibility of the ordinary finite arithmetic cases with the new
expression evaluator. The q=1, three-positive branch uses the proved cap 26. -/


set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace ThreeBoundConditionalNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ}



deriving instance DecidableEq for OrdinaryCase















end
end ThreeBoundConditionalNumeric




end
end Sensitivity213981Formal

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



























theorem b_condition_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j j' : L) (hjj' : j ≤  j') (v : ℕ) (h : BBound F i j v) : BBound F i j' v :=
  fun x hx => h x (hF j j' hjj' x hx)





















theorem b_min (F : L → (I → Bool) → Bool) (i j : L) (a b : ℕ)
    (ha : BBound F i j a) (hb : BBound F i j b) : BBound F i j (min a b) :=
  fun x hx => le_min (ha x hx) (hb x hx)















end
end ThreeBoundProfiles






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

@[simp] theorem eval_max {n : ℕ} (v : Profile n) (a b : Expr n) :
    (max a b).eval v = max (a.eval v) (b.eval v) := rfl





































































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
/- Exact coordinate and predicate bridge from the accepted ordinary proofs to
   the actual Bool-child family used by the current certificate. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem flipsTo_reindex_card (e : I ≃ J) (f : (I → Bool) → Bool)
    (b : Bool) (x : J → Bool) :
    (flipsTo (reindex e f) b x).card = (flipsTo f b (fun i => x (e i))).card := by
  have hs : (flipsTo (reindex e f) b x).map e.symm.toEmbedding =
      flipsTo f b (fun i => x (e i)) := by
    ext i
    simp only [Finset.mem_map_equiv,Equiv.symm_symm,flipsTo,
      Finset.mem_filter,Finset.mem_univ,true_and]
    change f (fun a => _root_.OAI.Paper320.flip x {e i} (e a))=b ↔ _
    rw [flip_reindex_singleton]
  simpa only [Finset.card_map] using congrArg Finset.card hs

variable {n k : ℕ}





theorem ordinary_archive_flips_card (S : Stage (Fin n) I (Fin k))
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
    (ell : Fin k → Fin k → Fin 2)
    (hAdj : ∀ v w, T.Adj v w ↔ S.Adj v w)
    (hLabel : ∀ v w, finTwoEquiv (ell v w)=S.label v w)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (b : Bool) (x : ((Fin k × Bool) × I) → Bool) :
    (flipsTo (ordinaryParent S F t g q) b x).card =
      (ThreeBoundOrdinaryArchive.ZT.flipsTo
        (ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q) b
          (fun a => x (ordinaryCoordEquiv a))).card := by
  rw [← ordinary_archive_eq S T ell hAdj hLabel F t g q]
  exact flipsTo_reindex_card _ _ _ _












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























end
end ThreeBoundHeadExpressions






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact expression and actual Boolean semantics of the 5591 ordinary branch. -/


set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000
set_option linter.unusedSectionVars false

namespace ThreeBoundOrdinary5591
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n k : ℕ} {I : Type} [Fintype I]



theorem ordinaryCase_finite : ∀ (q : Fin 9) (m : Fin 20) (u : Fin 18),
    4 ≤  q.val → (u.val+m.val).choose 2 ≤  q.val*u.val+(q.val+1)*m.val →
    u.val ≤  candidateTotalCap q.val m.val u.val →
    ordinaryCase numericCaps q.val m.val u.val=some (booleanOrdinaryCase q.val m.val u.val) := by
  decide +kernel

theorem booleanOrdinaryCase_mem (q qa m u : ℕ) (hq4 : 4 ≤  q) (hq : q ≤  8)
    (hm : m ≤  (if qa=q then 2*q+3 else 0)) (hu : u ≤  2*q+1)
    (hc : (u+m).choose 2 ≤  q*u+(q+1)*m) (hcap : u ≤  candidateTotalCap q m u) :
    booleanOrdinaryCase q m u ∈ ordinaryCases numericCaps q (qa == q) := by
  have hm' : m ≤  2*q+3 := by split_ifs at hm <;> omega
  have hcase := ordinaryCase_finite ⟨q,by omega⟩ ⟨m,by omega⟩ ⟨u,by omega⟩ hq4 hc hcap
  apply List.mem_flatMap.mpr
  refine ⟨m,?_,?_⟩
  · apply List.mem_range.mpr
    simpa only [beq_iff_eq] using (Nat.lt_succ_of_le hm)
  · apply List.mem_filterMap.mpr
    exact ⟨u,List.mem_range.mpr (by omega),hcase⟩

theorem positiveCaseCost_mono_j (q m u a b s j l : ℕ) (hjl : j ≤  l) :
    positiveCaseCost q m u a b s j ≤  positiveCaseCost q m u a b s l := by
  dsimp only [positiveCaseCost,ThreeBoundOrdinaryArchive.ZT.deletionCost]
  gcongr

theorem ordinaryAExpr_case_bound (v : Profile n) (ta ga qa tb gb q m u : ℕ)
    (hq4 : 4 ≤  q) (hq : q ≤  8)
    (hm : m ≤  (if qa=q then 2*q+3 else 0)) (hu : u ≤  2*q+1)
    (hc : (u+m).choose 2 ≤  q*u+(q+1)*m) (hcap : u ≤  candidateTotalCap q m u)
    (hskip : 0< u → gb ≠ ta) :
    positiveCaseCost q m u ((plusExpr n gb ta tb).eval v) ((aExpr n gb tb).eval v)
      ((bExpr n gb ga).eval v) ((bExpr n gb tb).eval v) ≤ 
      (ordinaryAExpr n numericCaps ta ga qa tb gb q).eval v := by
  have hmem := booleanOrdinaryCase_mem q qa m u hq4 hq hm hu hc hcap
  have hskip' : ¬ (0< u ∧ gb=ta) := by rintro ⟨hu,he⟩; exact hskip hu he
  simp only [ordinaryAExpr,if_neg (by omega : q≠0),Expr.eval_maximum,List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨booleanOrdinaryCase q m u,hmem,?_⟩
  simp only [Function.comp_apply,booleanOrdinaryCase,if_neg hskip',positiveCaseCost,
    ThreeBoundOrdinaryArchive.ZT.deletionCost,eval_add,eval_mul,eval_max]

/-- Actual Boolean-flip bound, for any realization of the uniform exclusions. -/
theorem ordinaryAExpr_bound (S : Stage (Fin n) I (Fin k))
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
    (ell : Fin k → Fin k → Fin 2)
    (hAdj : ∀ v w, T.Adj v w ↔ S.Adj v w)
    (hLabel : ∀ v w, finTwoEquiv (ell v w)=S.label v w)
    (hCaps : LabelCaps T ell)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ta tb ga gb : Fin n) (ht : ta ≤  tb) (hg : gb ≤  ga) (hga : ga ≤  ta)
    (qa q : ℕ) (hq : q ≤  qa) (hq4 : 4 ≤  q) (hq8 : q ≤  8)
    (v : Profile n) (hv : Upper F v)
    (x : ((Fin k × Bool) × I) → Bool)
    (hx : ordinaryParent S F ta ga qa x=false) :
    (flipsTo (ordinaryParent S F tb gb q) true x).card ≤ 
      (ordinaryAExpr n numericCaps ta.val ga.val qa tb.val gb.val q).eval v := by
  let a := (plusExpr n gb.val ta.val tb.val).eval v
  let b := (aExpr n gb.val tb.val).eval v
  let s := (bExpr n gb.val ga.val).eval v
  let j := (bExpr n gb.val tb.val).eval v
  have hgt : gb ≤  tb := hg.trans (hga.trans ht)
  have ha := ThreeBoundHeadExpressions.plusExpr_bound_all F hF v hv gb ta tb ht
  have hb := aExpr_bound F v hv gb tb hgt
  have hs := bExpr_bound F v hv gb ga hg
  have hj := bExpr_bound F v hv gb tb hgt
  have hj' : BBound F gb tb (min j s) := b_min F gb tb j s hj
    (b_condition_strengthen F hF gb ga tb (hga.trans ht) s hs)
  rw [ordinary_archive_flips_card S T ell hAdj hLabel F tb gb q true x]
  rw [← ordinary_archive_eq S T ell hAdj hLabel F ta ga qa] at hx
  dsimp only [reindex] at hx
  apply ordinary_positive_of_cases T ell hCaps F ⟨fun {i j} {y} hij hy => hF i j hij y hy⟩
    ta tb ga gb ht hg hga qa q hq hq4 hq8 a b s (min j s) _ (min_le_right _ _)
    ha hb hs hj' (x:=fun a => x (ordinaryCoordEquiv a)) (hx:=hx)
  intro m u hm hu hc hcap hskip
  exact (positiveCaseCost_mono_j q m u a b s (min j s) j (min_le_left _ _)).trans
    (ordinaryAExpr_case_bound v ta.val ga.val qa tb.val gb.val q m u hq4 hq8 hm hu hc hcap
      (fun hu he => hskip hu (Fin.ext he)))



end
end ThreeBoundOrdinary5591





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I] (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I (Fin k))
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (ell : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hAdj :
    ∀ (v w : Fin k),
      Iff
        (@Digraph.Adj.{0} (Fin k)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T) v w)
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I (Fin k) S v w))
  (hLabel :
    ∀ (v w : Fin k),
      @Eq.{1} Bool
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Bool)
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool
            (@Equiv.instEquivLike.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool))
          finTwoEquiv (ell v w))
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I (Fin k) S v w))
  (hCaps : @Sensitivity213981Formal.ThreeBoundOrdinary5591.LabelCaps k T ell) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (ta tb ga gb : Fin n) (ht : @LE.le.{0} (Fin n) (@instLEFin n) ta tb) (hg : @LE.le.{0} (Fin n) (@instLEFin n) gb ga)
  (hga : @LE.le.{0} (Fin n) (@instLEFin n) ga ta) (qa q : Nat) (hq : @LE.le.{0} Nat instLENat q qa)
  (hq4 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
  (hq8 : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) Bool) I → Bool)
  (hx :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent (Fin n) I (Fin k) (Fin.fintype k) S F ta ga qa x)
      Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} (Fin k) Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} (Fin k) Bool) I
          (@instFintypeProd.{0, 0} (Fin k) Bool (Fin.fintype k) Bool.fintype) inst)
        (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent (Fin n) I (Fin k) (Fin.fintype k) S F tb gb q)
        Bool.true x))
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundNumeric.ordinaryAExpr n
        Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps (@Fin.val n ta) (@Fin.val n ga) qa (@Fin.val n tb)
        (@Fin.val n gb) q)) := @Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinaryAExpr_bound
