-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.local_rank_cost
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:09:31.292307+00:00
-- url     : https://prove2.me/submissions/7e4c3abb-f550-43e4-a989-05ba5e854bb0

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxHeadLocal
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankExpressions
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
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



theorem bExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤  j) :
    BBound F i j ((bExpr n i.val j.val).eval v) := by
  simpa only [bExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.b i j) hij







end ThreeBoundNumeric





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact child-rank bounds, derived from the actual nested Boolean family.
These are the local profile inequalities used by the min/max rank oracle. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankProfiles
open OAI.Paper320 ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]





theorem rank_true (F : Fin n → (I → Bool) → Bool) (x : I → Bool) (r : Fin n)
    (hr : RankState F x r) : F r x = true := (hr r).2 le_rfl

theorem rank_false (F : Fin n → (I → Bool) → Bool) (x : I → Bool) (r k : Fin n)
    (hr : RankState F x r) (hk : r <  k) : F k x = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  exact (not_le_of_gt hk) ((hr k).1 hh)

theorem rank_next_false (F : Fin n → (I → Bool) → Bool) (x : I → Bool) (r : Fin n)
    (hr : RankState F x r) (hn : r.val+1 <  n) : F (next r) x = false := by
  apply rank_false F x r (next r) hr
  change r.val <  (next r).val
  rw [next_val r hn]
  omega



theorem downRank_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n) (hv : Upper F v)
    (x : I → Bool) (g r : Fin n) (hr : RankState F x r) (hgr : g ≤  r) :
    (flipsTo (F g) false x).card ≤  (downRankExpr n g.val r.val).eval v := by
  unfold downRankExpr
  split_ifs with hn
  · have hh := hv (.m g r) hgr hn x (rank_true F x r hr) (rank_next_false F x r hr hn)
    simpa only [mExpr,dif_pos g.isLt,dif_pos r.isLt,Expr.eval] using hh
  · exact bExpr_bound F v hv g r hgr x (rank_true F x r hr)

theorem upRank_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n) (hv : Upper F v)
    (x : I → Bool) (r k : Fin n) (hr : RankState F x r) (hrk : r <  k) :
    (flipsTo (F k) true x).card ≤  (pExpr n r.val k.val).eval v := by
  have hh := hv (.p r k) hrk x (rank_true F x r hr)
    (rank_next_false F x r hr (next_lt_n_of_lt r k hrk))
  simpa only [pExpr,dif_pos r.isLt,dif_pos k.isLt,Expr.eval] using hh

theorem unionRank_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n) (hv : Upper F v)
    (x : I → Bool) (g r k : Fin n) (hr : RankState F x r) (hgr : g ≤  r) (hrk : r <  k) :
    (flipsTo (F g) false x ∪ flipsTo (F k) true x).card ≤  (dExpr n g.val r.val k.val).eval v := by
  have hh := hv (.d g r k) hgr hrk x (rank_true F x r hr)
    (rank_next_false F x r hr (next_lt_n_of_lt r k hrk))
  simpa only [dExpr,dif_pos g.isLt,dif_pos r.isLt,dif_pos k.isLt,Expr.eval] using hh



theorem jointRank_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n) (hv : Upper F v)
    (x : I → Bool) (g r k : Fin n) (hr : RankState F x r) (hgr : g ≤  r) (hrk : r <  k) :
    (flipsTo (F g) false x ∪ flipsTo (F k) true x).card ≤ 
      (jointRankExpr n g.val r.val k.val).eval v := by
  change _ ≤  min ((dExpr n g.val r.val k.val).eval v)
    ((pExpr n r.val k.val).eval v+(downRankExpr n g.val r.val).eval v)
  apply le_min (unionRank_bound F v hv x g r k hr hgr hrk)
  have hh := (Finset.card_union_le (flipsTo (F g) false x) (flipsTo (F k) true x)).trans
    (Nat.add_le_add (downRank_bound F v hv x g r hr hgr) (upRank_bound F v hv x r k hr hrk))
  omega

theorem upRank_joint_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n) (hv : Upper F v)
    (x : I → Bool) (g r k : Fin n) (hr : RankState F x r) (hgr : g ≤  r) (hrk : r <  k) :
    (flipsTo (F k) true x).card ≤ 
      (min (pExpr n r.val k.val) (jointRankExpr n g.val r.val k.val)).eval v := by
  apply le_min (upRank_bound F v hv x r k hr hrk)
  exact (Finset.card_le_card Finset.subset_union_right).trans (jointRank_bound F v hv x g r k hr hgr hrk)

end
end ThreeBoundRankProfiles





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Shared actual-predicate interface for symmetric min/max transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



theorem mm_true (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=true ↔ F t x=true ∧ F t y=true ∧ (F u x=true ∨ F u y=true) := by
  simp only [mm,Bool.and_eq_true,Bool.or_eq_true,and_assoc]















end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual min/max downward transfer, with the upper-child improvement and
exact next-tier guard-destruction gate. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_left_eq_lower (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤  u) (y : I → Bool) (hy : F u y=true) :
    (fun x => mm F t u x y)=F t := by
  funext x
  have hyt := hF _ _ htu _ hy
  simp only [mm,hyt,hy,Bool.and_true,Bool.or_true]

theorem mm_left_eq_upper (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤  u) (y : I → Bool) (hyt : F t y=true) (hyu : F u y=false) :
    (fun x => mm F t u x y)=F u := by
  funext x
  simp only [mm,hyt,hyu,Bool.and_true,Bool.or_false]
  cases hu : F u x with
  | false => simp
  | true => simp only [hF _ _ htu _ hu,Bool.and_self]



















end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The rank oracle bounds the actual child repair sets, including the
union of target repair and guard destruction in the same child. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open OAI.Paper320 ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads ThreeBoundRankProfiles
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]



theorem local_rank_cost (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (x y : I → Bool)
    (rx ry g t u : Fin n) (hx : RankState F x rx) (hy : RankState F y ry)
    (hg : g ≤  rx) (htu : t ≤  u) (hoff : mm F t u x y=false)
    (e : Entry) (b : ℕ) (heG : g.val=e.guard)
    (heT : t.val=e.lowerAt b) (heU : u.val=e.upperAt b) :
    (flipsTo (fun z => mm F t u z y) true x).card ≤ 
        (rankUp n e (some b) rx.val ry.val).eval v ∧
    (flipsTo (fun z => mm F t u z y) true x ∪ flipsTo (F g) false x).card ≤ 
        (rankJoint n e (some b) rx.val ry.val).eval v := by
  by_cases htl : t ≤  ry
  · have hyt := (hy t).2 htl
    have htN : e.lowerAt b ≤  ry.val := by simpa only [← heT,Fin.le_def] using htl
    by_cases hul : u ≤  ry
    · have hyu := (hy u).2 hul
      have huN : e.upperAt b ≤  ry.val := by simpa only [← heU,Fin.le_def] using hul
      have he := mm_left_eq_lower F hF t u htu y hyu
      have hxt : F t x=false := by
        have hh := congrFun he x
        rw [hoff] at hh
        exact hh.symm
      have hrt : rx <  t := by
        by_contra hh
        have hon := (hx t).2 (le_of_not_gt hh)
        rw [hxt] at hon
        contradiction
      have hcond : rx.val <  e.lowerAt b ∧ e.lowerAt b <  n := by
        simpa only [← heT,Fin.lt_def] using And.intro hrt t.isLt
      simp only [rankUp,rankJoint,needed,if_pos htN,if_pos huN,if_pos hcond]
      rw [he,← heG,← heT]
      exact ⟨upRank_joint_bound F v hv x g rx t hx hg hrt,
        by simpa only [Finset.union_comm] using jointRank_bound F v hv x g rx t hx hg hrt⟩
    · have hyu : F u y=false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        exact hul ((hy u).1 hh)
      have huN : ¬ e.upperAt b ≤  ry.val := by simpa only [← heU,Fin.le_def] using hul
      have he := mm_left_eq_upper F hF t u htu y hyt hyu
      have hxu : F u x=false := by
        have hh := congrFun he x
        rw [hoff] at hh
        exact hh.symm
      have hru : rx <  u := by
        by_contra hh
        have hon := (hx u).2 (le_of_not_gt hh)
        rw [hxu] at hon
        contradiction
      have hcond : rx.val <  e.upperAt b ∧ e.upperAt b <  n := by
        simpa only [← heU,Fin.lt_def] using And.intro hru u.isLt
      simp only [rankUp,rankJoint,needed,if_pos htN,if_neg huN,if_pos hcond]
      rw [he,← heG,← heU]
      exact ⟨upRank_joint_bound F v hv x g rx u hx hg hru,
        by simpa only [Finset.union_comm] using jointRank_bound F v hv x g rx u hx hg hru⟩
  · have htN : ¬ e.lowerAt b ≤  ry.val := by simpa only [← heT,Fin.le_def] using htl
    have hyt : F t y=false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      exact htl ((hy t).1 hh)
    have hemp : flipsTo (fun z => mm F t u z y) true x=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hh := ((mm_true F t u _ _).1 (Finset.mem_filter.mp ha).2).2.1
      rw [hyt] at hh
      contradiction
    simp only [rankUp,rankJoint,needed,if_neg htN,lt_self_iff_false,and_false,if_false,
      hemp,Finset.card_empty,Finset.empty_union,eval_zero]
    exact ⟨le_rfl,by simpa only [← heG] using downRank_bound F v hv x g rx hx hg⟩



end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v) (x y : I → Bool) (rx ry g t u : Fin n)
  (hx : @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F x rx)
  (hy : @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F y ry)
  (hg : @LE.le.{0} (Fin n) (@instLEFin n) g rx) (htu : @LE.le.{0} (Fin n) (@instLEFin n) t u)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u x y) Bool.false)
  (e : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry) (b : Nat)
  (heG : @Eq.{1} Nat (@Fin.val n g) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard e))
  (heT : @Eq.{1} Nat (@Fin.val n t) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt e b))
  (heU : @Eq.{1} Nat (@Fin.val n u) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.upperAt e b)),
  And
    (@LE.le.{0} Nat instLENat
      (@Finset.card.{0} I
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst
          (fun (z : I → Bool) => @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u z y) Bool.true x))
      (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
        (Sensitivity213981Formal.ThreeBoundRankNumeric.rankUp n e (@Option.some.{0} Nat b) (@Fin.val n rx)
          (@Fin.val n ry))))
    (@LE.le.{0} Nat instLENat
      (@Finset.card.{0} I
        (@Union.union.{0} (Finset.{0} I)
          (@Finset.instUnion.{0} I fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst
            (fun (z : I → Bool) => @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u z y) Bool.true
            x)
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst (F g) Bool.false x)))
      (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
        (Sensitivity213981Formal.ThreeBoundRankNumeric.rankJoint n e (@Option.some.{0} Nat b) (@Fin.val n rx)
          (@Fin.val n ry)))) := @Sensitivity213981Formal.ThreeBoundRankNumeric.local_rank_cost
