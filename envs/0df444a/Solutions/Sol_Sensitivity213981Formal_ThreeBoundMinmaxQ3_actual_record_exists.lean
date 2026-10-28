-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxQ3.actual_record_exists
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:36:03.819715+00:00
-- url     : https://prove2.me/submissions/1a5bf5a8-028d-4930-8b37-5337ca2806b8

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
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
import Mathlib.Algebra.Order.BigOperators.Group.List
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ3_typed_tournament_covered
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_kind_target_prefix_iff


namespace Sensitivity213981Formal
section
/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TournamentHighRows
open scoped Classical BigOperators

variable {V X : Type}







theorem mem_arcs (R : V → V → Prop) (S : Finset V) (v w : V) :
    (v,w) ∈ arcs R S ↔ v ∈ S ∧ w ∈ S ∧ R v w := by
  classical
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hf.1
    exact ⟨hp.1, hp.2, hf.2⟩
  · rintro ⟨hv,hw,hR⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv,hw⟩,hR⟩

theorem reverse_arcs_card (R : V → V → Prop) (S : Finset V) :
    (arcs (fun v w => R w v) S).card = (arcs R S).card := by
  classical
  refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs _ S v w).1 hp with ⟨hv,hw,hR⟩
    exact (mem_arcs R S w v).2 ⟨hw,hv,hR⟩
  · intro p hp q hq heq
    exact Prod.swap_injective heq
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    exact ⟨(w,v), (mem_arcs _ S w v).2 ⟨hw,hv,hR⟩, rfl⟩

theorem arcs_disjoint_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : Disjoint (arcs R S) (arcs (fun v w => R w v) S) := by
  classical
  apply Finset.disjoint_left.mpr
  rintro ⟨v,w⟩ hp hq
  have hvw := ((mem_arcs R S v w).1 hp).2.2
  have hwv := ((mem_arcs _ S v w).1 hq).2.2
  have hne : v ≠ w := by
    intro he
    subst w
    exact hR.loopless v hvw
  exact ((hR.orient v w hne).1 hvw) hwv

theorem arcs_union_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) :
    arcs R S ∪ arcs (fun v w => R w v) S = S.offDiag := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  simp only [Finset.mem_union, mem_arcs, Finset.mem_offDiag]
  constructor
  · rintro (⟨hv,hw,hvw⟩ | ⟨hv,hw,hwv⟩)
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hvw
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hwv
  · rintro ⟨hv,hw,hne⟩
    by_cases hvw : R v w
    · exact Or.inl ⟨hv,hw,hvw⟩
    · exact Or.inr ⟨hv,hw,(hR.orient w v hne.symm).2 hvw⟩

/-- Every unordered pair contributes exactly one directed edge. -/
theorem twice_arcs_card (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : 2 * (arcs R S).card = S.card * S.card - S.card := by
  classical
  have h := Finset.card_union_of_disjoint (arcs_disjoint_reverse R hR S)
  rw [arcs_union_reverse R hR S, reverse_arcs_card R S, Finset.offDiag_card] at h
  omega

theorem arcs_eq_union_rows (R : V → V → Prop) (S : Finset V) :
    arcs R S = S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v)) := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  constructor
  · intro hp
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hv,Finset.mem_product.mpr ⟨Finset.mem_singleton_self v,?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hw,hR⟩
  · intro hp
    obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_product.mp hp with ⟨hvu,hw⟩
    have heq : v = u := Finset.mem_singleton.mp hvu
    subst u
    rcases Finset.mem_filter.mp hw with ⟨hw,hR⟩
    exact (mem_arcs R S v w).2 ⟨hu,hw,hR⟩

theorem arcs_card_le_sum_out (R : V → V → Prop) (S : Finset V) :
    (arcs R S).card ≤  ∑ v ∈ S, (outNeighbors R S v).card := by
  classical
  rw [arcs_eq_union_rows R S]
  calc
    (S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v))).card
        ≤  ∑ v ∈ S, (({v} : Finset V).product (outNeighbors R S v)).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ S, (outNeighbors R S v).card := by simp

/-- Necessary budget inequality for every finite tournament and every budget vector. -/
theorem budget_sum_bound (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) (budget : V → ℕ)
    (hbudget : ∀ v ∈ S, (outNeighbors R S v).card ≤  budget v) :
    S.card * (S.card - 1) ≤  2 * ∑ v ∈ S, budget v := by
  have hsum : (arcs R S).card ≤  ∑ v ∈ S, budget v :=
    (arcs_card_le_sum_out R S).trans (Finset.sum_le_sum hbudget)
  have htwice := Nat.mul_le_mul_left 2 hsum
  rw [twice_arcs_card R hR S] at htwice
  simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using htwice

theorem card_le_of_outdegree_le (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) (q : ℕ)
    (hbudget : ∀ v ∈ S, (outNeighbors R S v).card ≤  q) : S.card ≤  2*q+1 := by
  have hb := budget_sum_bound R hR S (fun _ => q) hbudget
  simp only [Finset.sum_const, nsmul_eq_mul] at hb
  by_cases hzero : S.card = 0
  · omega
  · have hpos : 0 <  S.card := Nat.pos_of_ne_zero hzero
    have hsub : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hpos
    by_contra hn
    have hlarge : 2*q+2 ≤  S.card := by omega
    have hmul := Nat.mul_le_mul_left S.card hlarge
    nlinarith

section GuardSemantics
variable [Fintype V]



/-- Every edge into a high head consumes an actual failed guard. -/
theorem out_high_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H : Finset V)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c)) (v : V) :
    outNeighbors R H v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwH,hvw⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw, hhigh w hwH (ell v w)⟩

/-- The finite high-row tournament bound, derived from actual selected guards. -/
theorem high_rows_card_le (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (H : Finset V) (q : ℕ)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ H, (guardFailures R ell P children v).card ≤  q) :
    H.card ≤  2*q+1 := by
  apply card_le_of_outdegree_le R hR H q
  intro v hv
  exact (Finset.card_le_card (out_high_subset_failures R ell P children H hhigh v)).trans
    (hbudget v hv)







/-- The positive-target prefix through tier b has at most 2b+1 high rows. -/
theorem positive_prefix_card_le (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (pref : Finset V) (b : ℕ)
    (hhigh : ∀ w ∈ pref, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ pref, (guardFailures R ell P children v).card ≤  b) :
    pref.card ≤  2*b+1 :=
  high_rows_card_le R hR ell P children pref b hhigh hbudget

end GuardSemantics
end TournamentHighRows








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

















theorem budget_le (q : ℕ) (k : Kind q) : budget q k ≤  q+1 := by
  have hk := k.isLt
  unfold budget
  split_ifs <;> omega





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















end
end ThreeBoundMinmaxTransfer




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
/- Actual high candidates of the Boolean construction admit one of the
kernel-covered sorted tournament records. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundActualEnumeration
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates ThreeBoundGradedCover
open scoped Classical BigOperators
noncomputable section

theorem card_filter_subtype {V : Type} [Fintype V] (H : Finset V) (p : V → Prop) :
    ((Finset.univ : Finset H).filter fun v => p v.val).card = (H.filter p).card := by
  classical
  apply Finset.card_bij (fun v _ => v.val)
  · intro v hv
    exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro v hv
    exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,rfl⟩

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

@[simp] theorem guardFailures_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    TournamentHighRows.guardFailures S.Adj S.label
      (fun z => F (S.guard j) z = true) (child x) v = failed S F j x v := by
  ext w
  simp [TournamentHighRows.guardFailures,failed]







end
end ThreeBoundActualEnumeration




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Candidate prefix caps for symmetric min/max targets. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCaps
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundPrefixCaps
open ThreeBoundActualEnumeration (guardFailures_eq)
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]



theorem prefix_guard_budget (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool)
    (q : ℕ) (v : V) (hv : v ∈ targetPrefix S F t u j x q) :
    (TournamentHighRows.guardFailures S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) v).card ≤  q := by
  rw [guardFailures_eq]
  obtain ⟨b,hb,ht⟩ := (Finset.mem_filter.mp hv).2
  exact ht.2.1.le.trans hb














end
end ThreeBoundMinmaxCaps



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact eleven-kind prefix identities for actual min/max candidates. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundAccounting ThreeBoundTypeCounts
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]



theorem prefix_high_eq
    (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤  3) (tag : V → Fin 11)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 3
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) (q : ℕ) :
    targetPrefix S F P.strongLower P.strongUpper j x q ∩
        highHeads S F P.strongLower P.strongUpper j x =
      (highHeads S F P.strongLower P.strongUpper j x).filter
        fun w => ThreeBoundHighTypes.positivePrefix 3 q (tag w)=true := by
  ext w
  simp only [Finset.mem_inter,Finset.mem_filter]
  constructor
  · rintro ⟨ht,hh⟩
    exact ⟨hh,(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).1 ht⟩
  · rintro ⟨hh,ht⟩
    exact ⟨(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).2 ht,hh⟩



















end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Every actual q3 min/max high-head configuration has a covered record. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxQ3
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundActualEnumeration (card_filter_subtype guardFailures_eq)
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem actual_record_exists (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hQ : S.tolerance j ≤  3)
    (tag : V → ThreeBoundQ3.Kind)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 3
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w))
    (hout : ∀ v ∈ highHeads S F P.strongLower P.strongUpper j x,
      ((highHeads S F P.strongLower P.strongUpper j x).filter (S.Adj v)).card ≤ 
        ThreeBoundQ3.budget (tag v)) :
    ∃ (ts : List ThreeBoundQ3.Kind) (ds : List Bool)
      (e : Fin ts.length ≃ highHeads S F P.strongLower P.strongUpper j x),
      ts.Pairwise (fun a b => ThreeBoundQ3.orderKey a≤ ThreeBoundQ3.orderKey b) ∧ (∀ k, ts.get k=tag (e k).val) ∧
      ds=ThreeBoundQ3.orientationBits (fun k l => S.Adj (e k).val (e l).val) ∧
      ThreeBoundQ3.record (ts,ds) ∈ ThreeBoundQ3.records := by
  let H := highHeads S F P.strongLower P.strongUpper j x
  let R : H → H → Prop := fun v w => S.Adj v.val w.val
  have hRH : TournamentHighRows.IsTournament R := by
    constructor
    · exact fun v => hR.loopless v.val
    · intro v w hvw
      exact hR.orient v.val w.val (fun h => hvw (Subtype.ext h))
  have hcard : H.card ≤  9 := by
    apply TournamentHighRows.card_le_of_outdegree_le S.Adj hR H 4
    intro w hw
    exact (hout w hw).trans (ThreeBoundHighTypes.budget_le 3 (tag w))
  apply ThreeBoundQ3.typed_tournament_covered R hRH (fun v => tag v.val)
  · simpa only [Fintype.card_coe] using hcard
  · intro q
    change ((Finset.univ : Finset H).filter fun v =>
      ThreeBoundQ3.positivePrefix q.val (tag v.val)=true).card ≤  _
    have hsub : ((Finset.univ : Finset H).filter fun v =>
        ThreeBoundQ3.positivePrefix q.val (tag v.val)=true).card =
        (H.filter fun v => ThreeBoundQ3.positivePrefix q.val (tag v)=true).card := by
      apply Finset.card_bij (fun v _ => v.val)
      · intro v hv
        exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
      · intro a _ b _ h
        exact Subtype.ext h
      · intro v hv
        exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,rfl⟩
    apply hsub.le.trans
    have he := ThreeBoundRankNumeric.prefix_high_eq S F hF i j P x hQ tag hk q.val
    change targetPrefix S F P.strongLower P.strongUpper j x q.val ∩ H = _ at he
    rw [← he]
    apply TournamentHighRows.positive_prefix_card_le S.Adj hR S.label
      (fun z => F (S.guard j) z=true) (child x) _ q.val
    · intro w hw
      exact high_guards_true S F hF i j P x w (Finset.mem_inter.mp hw).2
    · intro w hw
      exact prefix_guard_budget S F P.strongLower P.strongUpper j x q.val w (Finset.mem_inter.mp hw).1
  · intro v
    change ((Finset.univ : Finset H).filter fun w => S.Adj v.val w.val).card ≤  _
    rw [card_filter_subtype]
    exact hout v.val v.property

end
end ThreeBoundMinmaxQ3



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (hR :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S))
  (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (i j : L)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F i j)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (tag : V → Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (hk :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x)
          w →
        Sensitivity213981Formal.ThreeBoundHighTypes.OfKind (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.PositiveCandidate L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x w)
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.GuardCandidate L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x w)
          (tag w))
  (hout :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x)
          v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V
            (@Finset.filter.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v)
              (fun (a : V) =>
                Classical.propDecidable (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v a))
              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                j x)))
          (Sensitivity213981Formal.ThreeBoundQ3.budget (tag v))),
  @Exists.{1} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
    fun (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
    @Exists.{1} (List.{0} Bool) fun (ds : List.{0} Bool) =>
      @Exists.{1}
        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
          (@Subtype.{1} V fun (x_1 : V) =>
            @Membership.mem.{0, 0} V (Finset.{0} V)
              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                j x)
              x_1))
        fun
          (e :
            Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
              (@Subtype.{1} V fun (x_1 : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                      (@PartialOrder.toPreorder.{0} L
                        (@SemilatticeInf.toPartialOrder.{0} L
                          (@Lattice.toSemilatticeInf.{0} L
                            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                      S F i j P)
                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                      (@PartialOrder.toPreorder.{0} L
                        (@SemilatticeInf.toPartialOrder.{0} L
                          (@Lattice.toSemilatticeInf.{0} L
                            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                      S F i j P)
                    j x)
                  x_1)) =>
        And
          (@List.Pairwise.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (fun (a b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
            ts)
          (And
            (∀ (k : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
              @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts k)
                (tag
                  (@Subtype.val.{1} V
                    (fun (x_1 : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                            (@PartialOrder.toPreorder.{0} L
                              (@SemilatticeInf.toPartialOrder.{0} L
                                (@Lattice.toSemilatticeInf.{0} L
                                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                            S F i j P)
                          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                            (@PartialOrder.toPreorder.{0} L
                              (@SemilatticeInf.toPartialOrder.{0} L
                                (@Lattice.toSemilatticeInf.{0} L
                                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                            S F i j P)
                          j x)
                        x_1)
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (@Subtype.{1} V fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1))
                      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                      (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                        @Subtype.{1} V fun (x_2 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_2)
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (@Subtype.{1} V fun (x_1 : V) =>
                            @Membership.mem.{0, 0} V (Finset.{0} V)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                j x)
                              x_1))
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (@Subtype.{1} V fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@Equiv.instEquivLike.{1, 1}
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (@Subtype.{1} V fun (x_1 : V) =>
                            @Membership.mem.{0, 0} V (Finset.{0} V)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                j x)
                              x_1)))
                      e k))))
            (And
              (@Eq.{1} (List.{0} Bool) ds
                (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
                  (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
                  (fun (k l : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                    @Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e k))
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e l)))
                  fun (a b : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  Classical.propDecidable
                    (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e a))
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e b)))))
              (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
                Sensitivity213981Formal.ThreeBoundQ3.records
                (Sensitivity213981Formal.ThreeBoundQ3.record
                  (@Prod.mk.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (List.{0} Bool) ts ds))))) := @Sensitivity213981Formal.ThreeBoundMinmaxQ3.actual_record_exists
