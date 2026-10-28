-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.actual_kind_rankCost_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:42:08.751538+00:00
-- url     : https://prove2.me/submissions/eb61809b-dc9f-4911-ad16-1f425528ae40

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_HeadCosts
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxHeadLocal
import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankExpressions
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundHighTypes_positivePrefix_iff
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_mem_liftBits
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_possible
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_local_rank_cost
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
/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]





theorem hits_card_le_incoming (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) : (hits R ell G w).card ≤  incoming R G w :=
  Finset.card_image_le

theorem hits_card_le_two (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) : (hits R ell G w).card ≤  2 := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by decide)

theorem hits_card_le_capped (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) : (hits R ell G w).card ≤  min 2 (incoming R G w) :=
  le_min (hits_card_le_two R ell G w) (hits_card_le_incoming R ell G w)

theorem mem_hits (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) (c : Bool) :
    c ∈ hits R ell G w ↔ ∃ v ∈ G, R v w ∧ ell v w = c := by
  simp only [hits, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v,⟨hv,hR⟩,hc⟩
    exact ⟨v,hv,hR,hc⟩
  · rintro ⟨v,hv,hR,hc⟩
    exact ⟨v,⟨hv,hR⟩,hc⟩



















variable {L : Type} [Preorder L]













end
end ThreeBoundAccounting




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
/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes















theorem ofKind_high (q : ℕ) (P G : ℕ → Prop) (k : Kind q) (hk : OfKind q P G k) :
    (∃ b, P b) ∨ ∃ b, G b := by
  unfold OfKind at hk
  split_ifs at hk
  · exact Or.inl ⟨_,hk.1⟩
  · exact Or.inr ⟨_,hk.1⟩
  · exact Or.inl ⟨_,hk.1⟩







end ThreeBoundHighTypes




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual conditional boundary costs at one two-child head. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundHeadCharge
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



theorem headBits_card (v : V) (s : Bool → Finset I) :
    (headBits v s).card = (s false).card + (s true).card := by
  have hd : Disjoint (liftBits v false (s false)) (liftBits v true (s true)) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨⟨w,c⟩,a⟩ hx hy
    have hxf := (mem_liftBits v w false c a _).1 hx
    have hyt := (mem_liftBits v w true c a _).1 hy
    exact Bool.false_ne_true (hxf.2.1.symm.trans hyt.2.1)
  simp only [headBits,Finset.card_union_of_disjoint hd,card_liftBits]



theorem card_bool_finset (h : Finset Bool) :
    h.card = (if false ∈ h then 1 else 0) + (if true ∈ h then 1 else 0) := by
  have he : h = (if false ∈ h then {false} else ∅) ∪
      (if true ∈ h then {true} else ∅) := by
    ext b
    cases b <;> by_cases hf : false ∈ h <;> by_cases ht : true ∈ h <;> simp [hf,ht]
  rw [he]
  by_cases hf : false ∈ h <;> by_cases ht : true ∈ h <;> simp [hf,ht]



























end
end ThreeBoundHeadCharge





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

theorem failed_weak_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) : failed S F i x w ⊆ failed S F j x w := by
  intro z hz
  obtain ⟨_,hR,htrue⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,hF _ _ P.guards _ htrue⟩





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
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads ThreeBoundRankProfiles
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]





theorem upPart_rank_cost (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (x : Bool → I → Bool)
    (r : Bool → Fin n) (hr : ∀ d, RankState F (x d) (r d))
    (g t u : Fin n) (hg : ∀ d, g ≤  r d) (htu : t ≤  u)
    (hoff : mm F t u (x false) (x true)=false)
    (e : Entry) (b : ℕ) (heG : g.val=e.guard)
    (heT : t.val=e.lowerAt b) (heU : u.val=e.upperAt b) (d : Bool) :
    (upPart F t u x d).card ≤  (rankUp n e (some b) (r d).val (r (!d)).val).eval v ∧
    (upPart F t u x d ∪ flipsTo (F g) false (x d)).card ≤ 
      (rankJoint n e (some b) (r d).val (r (!d)).val).eval v := by
  apply local_rank_cost F hF v hv (x d) (x (!d)) (r d) (r (!d)) g t u
    (hr d) (hr (!d)) (hg d) htu _ e b heG heT heU
  cases d
  · exact hoff
  · simpa only [Bool.not_true,mm_comm] using hoff

end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual geometric target and guard candidates for monotone min/max rows. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCandidates
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]



















theorem high_guards_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (hw : w ∈ highHeads S F P.strongLower P.strongUpper j x) :
    ∀ c, F (S.guard j) (child x w c)=true := by
  rcases (Finset.mem_filter.mp hw).2 with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact hb.2
  · have hh := (mm_true F _ _ _ _).1 hb.2.2
    intro c
    cases c
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.1
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.2.1









theorem guard_failures_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (w : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x w b) :
    failed S F i x w=failed S F j x w := by
  have hs := failed_weak_subset S F hF i j P x w
  have hle := Finset.card_le_card hs
  have hnot : ¬ (failed S F i x w).card ≤  b := by
    intro hc
    have hmm := mm_mono F hF _ _ _ _ (P.lowerOrder b hb.1) (P.upperOrder b hb.1) _ _ hb.2.2
    have he := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
      P.weakDef x w b (hb.1.trans P.tolerances) hc hmm
    rw [hoff] at he
    contradiction
  apply Finset.eq_of_subset_of_card_le hs
  have hd := hb.2.1
  omega

theorem guard_hit_eligible (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (v : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x v b)
    (w : V) (hw : w ∈ failed S F j x v) : F (S.guard i) (child x w (S.label v w))=true := by
  rw [← guard_failures_eq S F hF i j P x hoff v b hb] at hw
  exact (Finset.mem_filter.mp hw).2.2



end
end ThreeBoundMinmaxCandidates





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
/- Every actual high head has an eligible rank state in the finite oracle. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundRankProfiles
open ThreeBoundMinmaxNumeric (EntryMatch)
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]







theorem positiveLevel_some (P G : ℕ → Prop) (k : Fin 11)
    (hk : ThreeBoundHighTypes.OfKind 3 P G k) (b : ℕ) (hb : positiveLevel k=some b) : P b := by
  unfold positiveLevel at hb
  split_ifs at hb with hlow hhigh
  · have he : k.val=b := Option.some.inj hb
    simp only [ThreeBoundHighTypes.OfKind,if_pos hlow] at hk
    exact he ▸ hk.1
  · have he : k.val-7=b := Option.some.inj hb
    have hn : ¬ k.val ≤  2*3+1 := by omega
    simp only [ThreeBoundHighTypes.OfKind,if_neg hlow,if_neg hn] at hk
    exact he ▸ hk.1

theorem positiveLevel_none (P G : ℕ → Prop) (d : ℕ) (k : Fin 11)
    (hp : ∀ b, P b → b ≤  3 ∧ d=b) (hg : ∀ b, G b → b ≤  3 ∧ d=b+1)
    (hk : ThreeBoundHighTypes.OfKind 3 P G k) (hn : positiveLevel k=none) : ¬ ∃ b, P b := by
  have hlow : ¬ k.val ≤  3 := by intro hh; simp [positiveLevel,hh] at hn
  have hhigh : ¬ 8 ≤  k.val := by intro hh; simp [positiveLevel,hlow,hh] at hn
  have he : ThreeBoundHighTypes.positivePrefix 3 3 k=false := by
    simp only [ThreeBoundHighTypes.positivePrefix,decide_eq_false_iff_not]
    omega
  rintro ⟨b,hb⟩
  have hh := (ThreeBoundHighTypes.positivePrefix_iff 3 d 3 P G k hp hg hk).1 ⟨b,(hp b hb).1,hb⟩
  rw [he] at hh
  contradiction

theorem rankCost_ge_state (a c : Entry) (k : Fin 11) (h : ℕ) (v : Profile n)
    (x y : Fin n) (hp : Possible a c k x.val y.val) :
    (stateCost n a c k x.val y.val h).eval v ≤  (rankCost n a c k h).eval v := by
  rw [rankCost,Expr.eval_maximum]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨stateCost n a c k x.val y.val h,?_,rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨x.val,List.mem_range.mpr x.isLt,?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨y.val,List.mem_range.mpr y.isLt,by simp only [if_pos hp]⟩

theorem possible_of_state (a c : Entry) (k : Fin 11)
    (x y : Fin n) (hp : Possible a c k x.val y.val) : possible n a c k=true := by
  apply List.any_eq_true.mpr
  refine ⟨x.val,List.mem_range.mpr x.isLt,?_⟩
  apply List.any_eq_true.mpr
  exact ⟨y.val,List.mem_range.mpr y.isLt,decide_eq_true hp⟩

end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Correlated target/guard unions give the rank-state high-head charge. -/


set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundRankProfiles
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundHeadCharge (headBits headBits_card guardParts card_bool_finset)
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem actual_parts_rank_cost (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (w : V) (hQ : S.tolerance j ≤  3) (k : Fin 11)
    (hk : ThreeBoundHighTypes.OfKind 3
      (PositiveCandidate S F P.strongLower P.strongUpper j x w)
      (GuardCandidate S F P.strongLower P.strongUpper j x w) k)
    (r : Bool → Fin n) (hr : ∀ z, RankState F (child x w z) (r z)) (z : Bool) :
    (targetParts S F P.strongLower P.strongUpper j x w z).card ≤ 
        (rankUp n c (positiveLevel k) (r z).val (r (!z)).val).eval v ∧
    (targetParts S F P.strongLower P.strongUpper j x w z ∪
        flipsTo (F (S.guard j)) false (child x w z)).card ≤ 
        (rankJoint n c (positiveLevel k) (r z).val (r (!z)).val).eval v := by
  have hw : w ∈ highHeads S F P.strongLower P.strongUpper j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ThreeBoundHighTypes.ofKind_high 3 _ _ k hk⟩
  have hg := high_guards_true S F hF i j P x w hw
  have hgr : ∀ z, S.guard j ≤  r z := fun z => (hr z (S.guard j)).1 (hg z)
  cases he : positiveLevel k with
  | none =>
    have hn := positiveLevel_none _ _ (failed S F j x w).card k
      (fun _ hh=>⟨hh.1.1.trans hQ,hh.1.2.1⟩) (fun _ hh=>⟨hh.1.trans hQ,hh.2.1⟩) hk he
    have ht : ¬ targetAt S F P.strongLower P.strongUpper j x w := by
      rintro ⟨b,hb⟩
      exact hn ⟨b,hb,hg⟩
    simp only [targetParts,if_neg ht,Finset.empty_union,Finset.card_empty,rankUp,rankJoint,eval_zero]
    exact ⟨le_rfl,by simpa only [hm.strongGuard] using downRank_bound F v hv _ _ (r z) (hr z) (hgr z)⟩
  | some b =>
    have hp := positiveLevel_some _ _ k hk b he
    have ht : targetAt S F P.strongLower P.strongUpper j x w := ⟨b,hp.1⟩
    simp only [targetParts,if_pos ht,hp.1.2.1]
    exact upPart_rank_cost F hF v hv (child x w) r hr (S.guard j)
      (P.strongLower b) (P.strongUpper b) hgr (P.strongLowerUpper b hp.1.1) hp.1.2.2.1
      c b hm.strongGuard (hm.strongLower b hp.1.1) (hm.strongUpper b hp.1.1) z

theorem stateCost_pair_bound (a c : Entry) (k : Fin 11) (x y h : ℕ) (v : Profile n)
    (T D : Bool → Finset I) (hit : Finset Bool) (w : V)
    (hc : hit.card ≤  h)
    (he0 : false ∈ hit → a.guard ≤  x) (he1 : true ∈ hit → a.guard ≤  y)
    (hu0 : (T false).card ≤  (rankUp n c (positiveLevel k) x y).eval v)
    (hu1 : (T true).card ≤  (rankUp n c (positiveLevel k) y x).eval v)
    (hj0 : (T false ∪ D false).card ≤  (rankJoint n c (positiveLevel k) x y).eval v)
    (hj1 : (T true ∪ D true).card ≤  (rankJoint n c (positiveLevel k) y x).eval v) :
    (headBits w (fun z => T z ∪ if z ∈ hit then D z else ∅)).card ≤ 
      (stateCost n a c k x y h).eval v := by
  rw [headBits_card]
  rw [card_bool_finset] at hc
  by_cases h0 : false ∈ hit <;> by_cases h1 : true ∈ hit
  · have he0' := he0 h0
    have he1' := he1 h1
    simp only [if_pos h0,if_pos h1] at hc ⊢
    simp only [stateCost,ThreeBoundMinmaxNumeric.eval_ite,eval_add,eval_max]
    split_ifs <;> omega
  · have he0' := he0 h0
    simp only [if_pos h0,if_neg h1,Finset.union_empty] at hc ⊢
    simp only [stateCost,ThreeBoundMinmaxNumeric.eval_ite,eval_add,eval_max]
    split_ifs <;> omega
  · have he1' := he1 h1
    simp only [if_neg h0,if_pos h1,Finset.union_empty] at hc ⊢
    simp only [stateCost,ThreeBoundMinmaxNumeric.eval_ite,eval_add,eval_max]
    split_ifs <;> omega
  · simp only [if_neg h0,if_neg h1,Finset.union_empty] at hc ⊢
    simp only [stateCost,ThreeBoundMinmaxNumeric.eval_ite,eval_add,eval_max]
    split_ifs <;> omega

theorem actual_kind_rankCost_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (w : V) (hQ : S.tolerance j ≤  3) (k : Fin 11)
    (hk : ThreeBoundHighTypes.OfKind 3
      (PositiveCandidate S F P.strongLower P.strongUpper j x w)
      (GuardCandidate S F P.strongLower P.strongUpper j x w) k) :
    possible n a c k=true ∧
    (headBits w (actualHeadParts S F P.strongLower P.strongUpper j x w)).card ≤ 
      (rankCost n a c k (min 2 (ThreeBoundAccounting.incoming S.Adj
        (guardSources S F P.strongLower P.strongUpper j x) w))).eval v := by
  have hw : w ∈ highHeads S F P.strongLower P.strongUpper j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ThreeBoundHighTypes.ofKind_high 3 _ _ k hk⟩
  have hg := high_guards_true S F hF i j P x w hw
  choose r hr hgr using fun z => exists_rank_of_true F hF (child x w z) (S.guard j) (hg z)
  have hp := actual_possible S F hF i j P a c hm x hoff w k hk r hr
  refine ⟨possible_of_state a c k (r false) (r true) hp,?_⟩
  apply le_trans (b := (stateCost n a c k (r false).val (r true).val
    (min 2 (ThreeBoundAccounting.incoming S.Adj
      (guardSources S F P.strongLower P.strongUpper j x) w))).eval v) _
    (rankCost_ge_state a c k _ v (r false) (r true) hp)
  have hb := actual_parts_rank_cost S F hF i j P a c hm v hv x w hQ k hk r hr
  have he : ∀ z ∈ hitChildren S F P.strongLower P.strongUpper j x w, a.guard ≤  (r z).val := by
    intro z hz
    obtain ⟨u,hu,hR,hl⟩ := (ThreeBoundAccounting.mem_hits _ _ _ w z).1 hz
    obtain ⟨b,hb'⟩ := (Finset.mem_filter.mp hu).2
    have hwf : w ∈ failed S F j x u := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hR,hg _⟩
    have hon := guard_hit_eligible S F hF i j P x hoff u b hb' w hwf
    rw [hl] at hon
    simpa only [← hm.weakGuard,Fin.le_def] using (hr z (S.guard i)).1 hon
  apply stateCost_pair_bound a c k (r false).val (r true).val _ v
    (targetParts S F P.strongLower P.strongUpper j x w)
    (fun z => flipsTo (F (S.guard j)) false (child x w z))
    (hitChildren S F P.strongLower P.strongUpper j x w) w
    (ThreeBoundAccounting.hits_card_le_capped S.Adj S.label _ w) (he false) (he true)
  · simpa only [Bool.not_false] using (hb false).1
  · simpa only [Bool.not_true] using (hb true).1
  · simpa only [Bool.not_false] using (hb false).2
  · simpa only [Bool.not_true] using (hb true).2

end
end ThreeBoundRankNumeric



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
  (a c : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F i x) Bool.false)
  (w : V)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
  (hk :
    Sensitivity213981Formal.ThreeBoundHighTypes.OfKind (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.PositiveCandidate (Fin n) I V inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x w)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.GuardCandidate (Fin n) I V inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x w)
      k),
  And (@Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankNumeric.possible n a c k) Bool.true)
    (@LE.le.{0} Nat instLENat
      (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@Sensitivity213981Formal.ThreeBoundHeadCharge.headBits I V w
          (@Sensitivity213981Formal.ThreeBoundMinmaxCover.actualHeadParts (Fin n) I V inst inst_1 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j x w)))
      (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
        (Sensitivity213981Formal.ThreeBoundRankNumeric.rankCost n a c k
          (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Sensitivity213981Formal.ThreeBoundAccounting.incoming V
              (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.guardSources (Fin n) I V inst_1 S F
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                  (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                  (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                j x)
              w))))) := @Sensitivity213981Formal.ThreeBoundRankNumeric.actual_kind_rankCost_bound
