-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxRank.rawBExpr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:36:40.052033+00:00
-- url     : https://prove2.me/submissions/35b150ee-df77-4e92-9d6e-2f1c2efb0d2f

import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankData
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_row_capacity_data
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_target_rank_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_capacity_B_row
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankProfiles_exists_rank_of_true


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









end ThreeBoundNumeric





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
/- Actual winning rows supply all feasible rank-capacity data used by the oracle. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxRank
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundConditional
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem sorted_row_ranks (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (t u : Fin n)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (hmm : mm F t u (child x w false) (child x w true)=true) :
    ∃ side : Bool, ∃ rx ry : Fin n,
      RankState F (child x w (!side)) rx ∧ RankState F (child x w side) ry ∧ rx≤ ry := by
  obtain ⟨hl,hr,_⟩ := (mm_true F t u _ _).1 hmm
  obtain ⟨r0,hr0,_⟩ := exists_rank_of_true F hF (child x w false) t hl
  obtain ⟨r1,hr1,_⟩ := exists_rank_of_true F hF (child x w true) t hr
  by_cases hle : r0≤ r1
  · exact ⟨true,r0,r1,hr0,hr1,hle⟩
  · exact ⟨false,r1,r0,hr1,hr0,le_of_not_ge hle⟩









end
end ThreeBoundMinmaxRank




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact-rank B expression bounds every actual min/max parent downward boundary. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxRank
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundConditional
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rankBTerm_bound (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (hF : Nested F) (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (hcount : (failed S F j x w).card≤ S.tolerance j)
    (hstrong : mm F (P.strongLower (failed S F j x w).card) (P.strongUpper (failed S F j x w).card)
      (child x w false) (child x w true)=true) :
    (flipsTo (parent S F i) false x).card≤ (rankBTerm n degree a c rx.val ry.val).eval v := by
  have hdata := row_capacity_data S F hF i j P a c hm x w side rx ry hx hy hxy hcount hstrong
  let da := capacityHeight a rx.val ry.val-1
  let db := capacityHeight c rx.val ry.val-1
  have hdbi : db≤ S.tolerance i := hdata.strong_tolerance.trans P.tolerances
  have hweakdb := mm_mono F hF _ _ _ _ (P.lowerOrder db hdata.strong_tolerance)
    (P.upperOrder db hdata.strong_tolerance) _ _ hdata.strong_target
  have htarget := target_rank_bound F hF v hv a db (P.weakLower db) (P.weakUpper db)
    (P.weakLowerUpper db hdbi) (hm.weakLower db hdbi) (hm.weakUpper db hdbi)
    x w side rx ry hx hy hxy hweakdb
  have hA := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hh := minmax_capacity_B_row S F hF i j P x w da db degree _ _ hdata.guard_count
    hdata.strong_tolerance hdata.strong_target hdata.weak_tolerance hdata.capacity_order hdata.weak_target
    (hd w) htarget hA
  have heq : (capacityHeight a rx.val ry.val=capacityHeight c rx.val ry.val) ↔ da=db := by
    dsimp [da,db]
    have hpa := hdata.weak_pos
    have hpc := hdata.strong_pos
    omega
  have hne : capacityHeight c rx.val ry.val≠0 := Nat.ne_of_gt hdata.strong_pos
  have hneed := And.intro hdata.need_lower hdata.need_upper
  unfold rankBTerm
  rw [if_neg hne,if_pos hneed]
  simpa only [ThreeBoundMinmaxNumeric.eval_ite,eval_add,eval_mul,eval_zero,heq,hm.weakGuard,hm.strongGuard] using hh

theorem rawBExpr_bound (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (hF : Nested F) (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree) (v : Profile n) (hv : Upper F v) :
    BBound (parent S F) i j ((rawBExpr n degree a c).eval v) := by
  intro x hxj
  obtain ⟨w,hcount,hstrong⟩ := (parent_true_iff S F j x).1 hxj
  rw [P.strongDef] at hstrong
  obtain ⟨side,rx,ry,hrx,hry,hxy⟩ := sorted_row_ranks F hF _ _ x w hstrong
  have hh := rankBTerm_bound S F hF i j P a c hm degree hd v hv x w side rx ry hrx hry hxy hcount hstrong
  apply hh.trans
  rw [rawBExpr,Expr.eval_maximum]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨rankBTerm n degree a c rx.val ry.val,?_,rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨rx.val,List.mem_range.mpr rx.isLt,?_⟩
  apply List.mem_map.mpr
  exact ⟨ry.val,mem_interval.mpr ⟨hxy,ry.isLt⟩,rfl⟩

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
  (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (a c : Sensitivity213981Formal.ThreeBoundMinmaxRank.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c) (degree : Nat)
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
      (Sensitivity213981Formal.ThreeBoundMinmaxRank.rawBExpr n degree a c)) := @Sensitivity213981Formal.ThreeBoundMinmaxRank.rawBExpr_bound
