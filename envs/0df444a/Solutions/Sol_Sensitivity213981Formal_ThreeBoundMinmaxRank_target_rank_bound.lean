-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxRank.target_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:06.935996+00:00
-- url     : https://prove2.me/submissions/c6cbf804-659a-4dfb-9353-0ad58e72acb6

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_mmTargetBits_eq_oriented


namespace Sensitivity213981Formal
section
/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _

























end
end ThreeBoundPositive






end
end Sensitivity213981Formal

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








@[simp] theorem eval_add {n : ℕ} (v : Profile n) (a b : Expr n) :
    (a+b).eval v = a.eval v+b.eval v := rfl









































































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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



theorem mm_true (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=true ↔ F t x=true ∧ F t y=true ∧ (F u x=true ∨ F u y=true) := by
  simp only [mm,Bool.and_eq_true,Bool.or_eq_true,and_assoc]

theorem mm_comm (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=mm F t u y x := by
  simp only [mm,Bool.and_comm,Bool.or_comm]













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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









theorem orientedBits_card (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a b : ℕ)
    (ha : (flipsTo (F t) false (child x w (!c))).card ≤  a)
    (hb : (flipsTo (F u) false (child x w c)).card ≤  b) :
    (orientedBits F t u x w c).card ≤  a+b := by
  exact (Finset.card_union_le _ _).trans (by simpa only [card_liftBits] using Nat.add_le_add ha hb)













end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact rank states, numeric capacities and actual private-target boundaries. -/


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











theorem mm_rank_iff (F : Fin n → (I → Bool) → Bool) (t u : Fin n)
    (x y : I → Bool) (rx ry : Fin n) (hx : RankState F x rx) (hy : RankState F y ry) (hxy : rx≤ ry) :
    mm F t u x y=true ↔ t≤ rx ∧ u≤ ry := by
  rw [mm_true]
  constructor
  · rintro ⟨htx,hty,hu⟩
    exact ⟨(hx t).1 htx,hu.elim (fun hh => ((hx u).1 hh).trans hxy) (fun hh => (hy u).1 hh)⟩
  · rintro ⟨ht,hu⟩
    exact ⟨(hx t).2 ht,(hy t).2 (ht.trans hxy),Or.inr ((hy u).2 hu)⟩

theorem mm_reorder (F : Fin n → (I → Bool) → Bool) (t u : Fin n)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) :
    mm F t u (child x w false) (child x w true)=mm F t u (child x w (!c)) (child x w c) := by
  cases c
  · exact mm_comm F t u _ _
  · rfl

theorem mm_row_rank_iff (F : Fin n → (I → Bool) → Bool) (t u : Fin n)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!c)) rx) (hy : RankState F (child x w c) ry) (hxy : rx≤ ry) :
    mm F t u (child x w false) (child x w true)=true ↔ t≤ rx ∧ u≤ ry := by
  rw [mm_reorder F t u x w c]
  exact mm_rank_iff F t u _ _ rx ry hx hy hxy







theorem target_rank_bound (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (e : Entry) (d : ℕ) (t u : Fin n) (htu : t≤ u)
    (ht : t.val=e.lowerAt d) (hu : u.val=e.upperAt d)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (hmm : mm F t u (child x w false) (child x w true)=true) :
    (mmTargetBits F t u x w).card ≤ 
      (downRankExpr n (need n e ry.val d) rx.val+downRankExpr n (need n e rx.val d) ry.val).eval v := by
  obtain ⟨htrx,hury⟩ := (mm_row_rank_iff F t u x w side rx ry hx hy hxy).1 hmm
  have htlo := (hx t).2 htrx
  have huhi := (hy u).2 hury
  have htry := htrx.trans hxy
  rw [mmTargetBits_eq_oriented F hF t u htu x w side huhi htlo]
  by_cases hulo : u≤ rx
  · have hulotrue := (hx u).2 hulo
    rw [if_pos hulotrue]
    have hh := orientedBits_card F t t x w side _ _
      (downRank_bound F v hv _ t rx hx htrx) (downRank_bound F v hv _ t ry hy htry)
    simpa only [need,← ht,← hu,if_pos (show t.val≤ ry.val from htry),if_pos (show u.val≤ ry.val from hury),
      if_pos (show t.val≤ rx.val from htrx),if_pos (show u.val≤ rx.val from hulo),eval_add] using hh
  · have hulofalse := rank_false F _ rx u hx (lt_of_not_ge hulo)
    have huntrue : ¬F u (child x w (!side))=true := by rw [hulofalse]; decide
    rw [if_neg huntrue]
    have hh := orientedBits_card F t u x w side _ _
      (downRank_bound F v hv _ t rx hx htrx) (downRank_bound F v hv _ u ry hy hury)
    simpa only [need,← ht,← hu,if_pos (show t.val≤ ry.val from htry),if_pos (show u.val≤ ry.val from hury),
      if_pos (show t.val≤ rx.val from htrx),if_neg (show ¬u.val≤ rx.val from hulo),eval_add] using hh

end
end ThreeBoundMinmaxRank




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [Fintype.{0} V] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (e : Sensitivity213981Formal.ThreeBoundMinmaxRank.Entry) (d : Nat) (t u : Fin n)
  (htu : @LE.le.{0} (Fin n) (@instLEFin n) t u)
  (ht : @Eq.{1} Nat (@Fin.val n t) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt e d))
  (hu : @Eq.{1} Nat (@Fin.val n u) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.upperAt e d))
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (side : Bool) (rx ry : Fin n)
  (hx :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not side)) rx)
  (hy :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w side) ry)
  (hxy : @LE.le.{0} (Fin n) (@instLEFin n) rx ry)
  (hmm :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.true))
      Bool.true),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits (Fin n) I V inst F t u x w))
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (@HAdd.hAdd.{0, 0, 0} (Sensitivity213981Formal.ThreeBoundNumeric.Expr n)
        (Sensitivity213981Formal.ThreeBoundNumeric.Expr n) (Sensitivity213981Formal.ThreeBoundNumeric.Expr n)
        (@instHAdd.{0} (Sensitivity213981Formal.ThreeBoundNumeric.Expr n)
          (@Sensitivity213981Formal.ThreeBoundNumeric.instAddExpr_q2RawExpressions n))
        (Sensitivity213981Formal.ThreeBoundRankProfiles.downRankExpr n
          (Sensitivity213981Formal.ThreeBoundMinmaxRank.need n e (@Fin.val n ry) d) (@Fin.val n rx))
        (Sensitivity213981Formal.ThreeBoundRankProfiles.downRankExpr n
          (Sensitivity213981Formal.ThreeBoundMinmaxRank.need n e (@Fin.val n rx) d) (@Fin.val n ry)))) := @Sensitivity213981Formal.ThreeBoundMinmaxRank.target_rank_bound
