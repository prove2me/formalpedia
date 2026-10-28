-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.actual_possible
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:25:41.363035+00:00
-- url     : https://prove2.me/submissions/24c32252-f11e-4a2e-b584-7845422daad2

import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxHeadLocal
import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankExpressions
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
/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes













theorem ofKind_count (q d : ℕ) (P G : ℕ → Prop) (k : Kind q)
    (hp : ∀ b, P b → d=b) (hg : ∀ b, G b → d=b+1) (hk : OfKind q P G k) :
    d=budget q k := by
  unfold OfKind at hk
  unfold budget
  split_ifs at hk ⊢ with h1 h2
  · exact hp _ hk.1
  · have h := hg _ hk.1
    omega
  · exact hp _ hk.1

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

theorem target_iff_rank (F : Fin n → (I → Bool) → Bool)
    (x y : I → Bool) (rx ry t u : Fin n) (hx : RankState F x rx) (hy : RankState F y ry)
    (e : Entry) (b : ℕ) (ht : t.val=e.lowerAt b) (hu : u.val=e.upperAt b) :
    mm F t u x y=true ↔ target e b rx.val ry.val := by
  rw [mm_true,hx t,hy t,hx u,hy u]
  change t.val ≤  rx.val ∧ t.val ≤  ry.val ∧ (u.val ≤  rx.val ∨ u.val ≤  ry.val) ↔ _
  simp only [target,ht,hu]





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















end
end ThreeBoundMinmaxCandidates





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

theorem positive_rank_iff (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (i j : Fin n) (P : PairData S F i j)
    (a c : Entry) (hm : EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (w : V) (r : Bool → Fin n)
    (hr : ∀ z, RankState F (child x w z) (r z))
    (hg : ∀ z, F (S.guard j) (child x w z)=true)
    (d : ℕ) (hd : (failed S F j x w).card=d) (b : ℕ) :
    PositiveCandidate S F P.strongLower P.strongUpper j x w b ↔
      positiveState c d (r false).val (r true).val b := by
  constructor
  · intro hb
    have hmm := target_iff_rank F _ _ _ _ (P.strongLower b) (P.strongUpper b)
      (hr false) (hr true) c b (hm.strongLower b hb.1.1) (hm.strongUpper b hb.1.1)
    refine ⟨by simpa only [← hm.strongTolerance] using hb.1.1,hd.symm.trans hb.1.2.1,?_,?_⟩
    · intro hh
      have hon := hmm.2 hh
      rw [hb.1.2.2.1] at hon
      contradiction
    · rcases hb.1.2.2.2 with hh | hh
      · have he := (hr false (P.strongLower b)).1 hh
        exact Or.inl (by simpa only [← hm.strongLower b hb.1.1,Fin.le_def] using he)
      · have he := (hr true (P.strongLower b)).1 hh
        exact Or.inr (by simpa only [← hm.strongLower b hb.1.1,Fin.le_def] using he)
  · intro hb
    have hbq : b ≤  S.tolerance j := by simpa only [hm.strongTolerance] using hb.1
    have hmm := target_iff_rank F _ _ _ _ (P.strongLower b) (P.strongUpper b)
      (hr false) (hr true) c b (hm.strongLower b hbq) (hm.strongUpper b hbq)
    refine ⟨⟨hbq,hd.trans hb.2.1,?_,?_⟩,hg⟩
    · exact Bool.eq_false_iff.mpr (fun hh => hb.2.2.1 (hmm.1 hh))
    · rcases hb.2.2.2 with hh | hh
      · exact Or.inl ((hr false (P.strongLower b)).2
          (by simpa only [← hm.strongLower b hbq,Fin.le_def] using hh))
      · exact Or.inr ((hr true (P.strongLower b)).2
          (by simpa only [← hm.strongLower b hbq,Fin.le_def] using hh))

theorem guard_rank_iff (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (i j : Fin n) (P : PairData S F i j)
    (a c : Entry) (hm : EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (w : V) (r : Bool → Fin n)
    (hr : ∀ z, RankState F (child x w z) (r z))
    (d : ℕ) (hd : (failed S F j x w).card=d) (b : ℕ) :
    GuardCandidate S F P.strongLower P.strongUpper j x w b ↔
      guardState c d (r false).val (r true).val b := by
  constructor
  · intro hb
    refine ⟨by simpa only [← hm.strongTolerance] using hb.1,hd.symm.trans hb.2.1,?_⟩
    exact (target_iff_rank F _ _ _ _ (P.strongLower b) (P.strongUpper b)
      (hr false) (hr true) c b (hm.strongLower b hb.1) (hm.strongUpper b hb.1)).1 hb.2.2
  · intro hb
    have hbq : b ≤  S.tolerance j := by simpa only [hm.strongTolerance] using hb.1
    refine ⟨hbq,hd.trans hb.2.1,?_⟩
    exact (target_iff_rank F _ _ _ _ (P.strongLower b) (P.strongUpper b)
      (hr false) (hr true) c b (hm.strongLower b hbq) (hm.strongUpper b hbq)).2 hb.2.2

theorem actual_possible (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false)
    (w : V) (k : Fin 11)
    (hk : ThreeBoundHighTypes.OfKind 3
      (PositiveCandidate S F P.strongLower P.strongUpper j x w)
      (GuardCandidate S F P.strongLower P.strongUpper j x w) k)
    (r : Bool → Fin n) (hr : ∀ z, RankState F (child x w z) (r z)) :
    Possible a c k (r false).val (r true).val := by
  have hw : w ∈ highHeads S F P.strongLower P.strongUpper j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ThreeBoundHighTypes.ofKind_high 3 _ _ k hk⟩
  have hg := high_guards_true S F hF i j P x w hw
  have hd : (failed S F j x w).card=ThreeBoundHighTypes.budget 3 k :=
    ThreeBoundHighTypes.ofKind_count 3 _ _ _ k (fun _ hh=>hh.1.2.1) (fun _ hh=>hh.2.1) hk
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [← hm.strongGuard,Fin.le_def] using (hr false (S.guard j)).1 (hg false)
  · simpa only [← hm.strongGuard,Fin.le_def] using (hr true (S.guard j)).1 (hg true)
  · intro ha ht
    have ha' : ThreeBoundHighTypes.budget 3 k ≤  S.tolerance i := by
      simpa only [hm.weakTolerance] using ha
    have hon := (target_iff_rank F _ _ _ _ (P.weakLower _) (P.weakUpper _)
      (hr false) (hr true) a _ (hm.weakLower _ ha') (hm.weakUpper _ ha')).2 ht
    have hc := (Finset.card_le_card (failed_weak_subset S F hF i j P x w)).trans hd.le
    have he := parent_true_of_count S F hF i P.weakLower P.weakUpper
      P.weakLowerMono P.weakUpperMono P.weakDef x w _ ha' hc hon
    rw [hoff] at he
    contradiction
  · have hp := positive_rank_iff S F i j P a c hm x w r hr hg _ hd
    have hgg := guard_rank_iff S F i j P a c hm x w r hr _ hd
    unfold ThreeBoundHighTypes.OfKind at hk ⊢
    simpa only [← hp,← hgg] using hk









end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
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
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst S F i x) Bool.false) (w : V)
  (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
  (hk :
    Sensitivity213981Formal.ThreeBoundHighTypes.OfKind (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.PositiveCandidate (Fin n) I V inst S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x w)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.GuardCandidate (Fin n) I V inst S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x w)
      k)
  (r : Bool → Fin n)
  (hr :
    ∀ (z : Bool),
      @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w z) (r z)),
  Sensitivity213981Formal.ThreeBoundRankNumeric.Possible a c k (@Fin.val n (r Bool.false)) (@Fin.val n (r Bool.true)) := @Sensitivity213981Formal.ThreeBoundRankNumeric.actual_possible
