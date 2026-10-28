-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxRank.rejected_capacity_le_count
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:23.94043+00:00
-- url     : https://prove2.me/submissions/cd80f99b-856b-414f-be80-4a5e59ec6dd7

import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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

theorem accepted_spec (e : Entry) (d x y : ℕ) :
    accepted e d x y=true ↔ e.lowerAt d≤ x ∧ e.upperAt d≤ y := by
  simp only [accepted,decide_eq_true_eq]





theorem capacity_positive_data (e : Entry) (x y : ℕ) (hpos : 0< capacityHeight e x y) :
    capacityHeight e x y-1≤ e.tolerance ∧ accepted e (capacityHeight e x y-1) x y=true := by
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup (Finset.range (e.tolerance+1))
    ⟨0,Finset.mem_range.mpr (by omega)⟩ (fun k => if accepted e k x y then k+1 else 0)
  change capacityHeight e x y=(if accepted e d x y then d+1 else 0) at he
  by_cases ha : accepted e d x y=true
  · rw [if_pos ha] at he
    have hd' : d< e.tolerance+1 := Finset.mem_range.mp hd
    have hdEq : capacityHeight e x y-1=d := by omega
    exact ⟨by omega,hdEq.symm ▸ ha⟩
  · rw [if_neg ha] at he
    omega



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



theorem matched_accepted_strong (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (d : ℕ) (hd : d≤ S.tolerance j) :
    mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true ↔
      accepted c d rx.val ry.val=true := by
  rw [mm_row_rank_iff F _ _ x w side rx ry hx hy hxy,accepted_spec]
  change ((P.strongLower d).val≤ rx.val ∧ (P.strongUpper d).val≤ ry.val) ↔ _
  rw [hm.strongLower d hd,hm.strongUpper d hd]





end
end ThreeBoundMinmaxRank




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









theorem rejected_capacity_le_count (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (hF : Nested F) (j k : Fin n) (P : PairData S F j k) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F j k P a c)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (hoff : parent S F k x=false) : capacityHeight c rx.val ry.val≤ (failed S F k x w).card := by
  by_cases hpos : 0< capacityHeight c rx.val ry.val
  · obtain ⟨hdb,hacc⟩ := capacity_positive_data c rx.val ry.val hpos
    have hdb' : capacityHeight c rx.val ry.val-1≤ S.tolerance k := by simpa only [hm.strongTolerance] using hdb
    have htarget := (matched_accepted_strong S F j k P a c hm x w side rx ry hx hy hxy _ hdb').2 hacc
    by_contra hn
    have hcount : (failed S F k x w).card≤ capacityHeight c rx.val ry.val-1 := by omega
    have hon := parent_true_of_count S F hF k P.strongLower P.strongUpper P.strongLowerMono P.strongUpperMono
      P.strongDef x w _ hdb' hcount htarget
    rw [hoff] at hon
    contradiction
  · omega

end
end ThreeBoundMinmaxRank




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
  (j k : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F j k)
  (a c : Sensitivity213981Formal.ThreeBoundMinmaxRank.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F j k P a c)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (side : Bool) (rx ry : Fin n)
  (hx :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not side)) rx)
  (hy :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w side) ry)
  (hxy : @LE.le.{0} (Fin n) (@instLEFin n) rx ry)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst S F k x) Bool.false),
  @LE.le.{0} Nat instLENat
    (Sensitivity213981Formal.ThreeBoundMinmaxRank.capacityHeight c (@Fin.val n rx) (@Fin.val n ry))
    (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst S F k x w)) := @Sensitivity213981Formal.ThreeBoundMinmaxRank.rejected_capacity_le_count
