-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.actual_capPrefix
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:26:09.903987+00:00
-- url     : https://prove2.me/submissions/7197fdc3-663e-49ad-9d3a-9734af072ea8

import Definitions.Def_Sensitivity213981Formal_ActualPrefixCaps
import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
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
import Theorems.Thm_Sensitivity213981Formal_ResidualCaps_actual_dominator_residual_cap
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMarkers_exists_markers_of_sorted_prefix
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCaps_actual_marked_prefix_cap
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPrefixCaps_ordinary_prefix_cap
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_zero_marked_prefix_cap
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_capPrefix_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_kind_target_prefix_iff


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

















theorem sum_grouped (H : Finset V) (tag : V → K) (f : K → ℕ) :
    (∑ v ∈ H, f (tag v)) = ∑ k, typeCount H tag k*f k := by
  classical
  simpa [typeCount, Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise' H tag f).symm













variable {L : Type} [Preorder L]













end
end ThreeBoundAccounting




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The sorted residual prefixes in the case records are sums over actual
distinct marker subsets, not merely optimistic numerical minima. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundMarkers
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [DecidableEq V]





/-- Any cap valid for every chosen k-marker set is valid for the exact
    residual prefix stored in the complete tournament record. -/
theorem bound_by_sorted_prefix (vs : List V) (hvs : vs.Nodup)
    (res : V → ℕ) (k a c : ℕ) (hk : k ≤  vs.length)
    (hcap : ∀ M : Finset V, M ⊆ vs.toFinset → M.card = k →
      a ≤  c+∑ v ∈ M, res v) :
    a ≤  c+(((vs.map res).mergeSort (· ≤  ·)).take k).sum := by
  obtain ⟨M,hM,hcard,hsum⟩ := exists_markers_of_sorted_prefix vs hvs res k hk
  simpa only [hsum] using hcap M hM hcard

end
end ThreeBoundMarkers




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









end ThreeBoundHighTypes




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundTypeCounts
open ThreeBoundAccounting
open scoped Classical BigOperators
noncomputable section
variable {V K : Type} [Fintype V] [Fintype K]

theorem card_filter_tag (H : Finset V) (tag : V → K) (p : K → Prop) :
    (H.filter fun v => p (tag v)).card =
      ∑ k, if p k then typeCount H tag k else 0 := by
  classical
  have hh := sum_grouped H tag (fun k => if p k then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hh
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact hh

theorem sum_typeCounts (H : Finset V) (tag : V → K) :
    (∑ k, typeCount H tag k) = H.card := by
  classical
  simpa using (sum_grouped H tag (fun _ => 1)).symm





end
end ThreeBoundTypeCounts

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

theorem target_some_guard (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (b : ℕ) (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b) :
    F (S.guard j) (child x w false)=true ∨ F (S.guard j) (child x w true)=true :=
  hb.2.2.2.elim (fun hh => Or.inl (hF _ _ (P.guardTarget b hb.1) _ hh))
    (fun hh => Or.inr (hF _ _ (P.guardTarget b hb.1) _ hh))

theorem target_partner_guard (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (b : ℕ) (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b)
    (c : Bool) (hc : c ≠ missing S F j x w) : F (S.guard j) (child x w c)=true := by
  have hh := target_some_guard S F hF i j P x w b hb
  unfold missing at hc
  cases c <;> split_ifs at hc with he <;> simp_all











end
end ThreeBoundMinmaxCandidates





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- All prefix-cap ingredients are consequences of actual failed-guard sets
and the separately proved labeling exclusions. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundPrefixCaps
open scoped Classical BigOperators
open TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
open MarkedCandidateCaps ThreeBoundMarkers
noncomputable section
variable {V X : Type} [Fintype V] [DecidableEq V]









theorem dominator_prefix_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (color : V → Bool) (vs : List V)
    (hvs : vs.Nodup) (hH : vs.toFinset = H)
    (m a : ℕ) (hm : m ≤  vs.length) (hcap : DominatorCardBound R ell m a)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → P (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell P children v).card = 0) :
    T.card ≤  (T ∩ H).card+(a-1)+
      (((vs.map (residual R ell P children H)).mergeSort (· ≤  ·)).take m).sum := by
  have hN := bound_by_sorted_prefix vs hvs (residual R ell P children H)
    m (T \ H).card (a-1) hm (by
      intro M hM hc
      rw [hH] at hM
      exact actual_dominator_residual_cap R hR ell P children (T \ H) H M
        Finset.sdiff_disjoint hM color m a hc hcap
        (fun w hw => hpartner w (Finset.mem_sdiff.mp hw).1) hhigh
        (fun v hv => hT v (Finset.mem_sdiff.mp hv).1))
  have hsplit := Finset.card_sdiff_add_card_inter T H
  omega



end
end ThreeBoundPrefixCaps






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

theorem prefix_partner (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q : ℕ) (w : V)
    (hw : w ∈ targetPrefix S F P.strongLower P.strongUpper j x q)
    (c : Bool) (hc : c ≠ missing S F j x w) :
    F (S.guard j) (child x w c)=true := by
  obtain ⟨b,hb,ht⟩ := (Finset.mem_filter.mp hw).2
  exact target_partner_guard S F hF i j P x w b ht c hc

theorem prefix_guard_budget (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool)
    (q : ℕ) (v : V) (hv : v ∈ targetPrefix S F t u j x q) :
    (TournamentHighRows.guardFailures S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) v).card ≤  q := by
  rw [guardFailures_eq]
  obtain ⟨b,hb,ht⟩ := (Finset.mem_filter.mp hv).2
  exact ht.2.1.le.trans hb

theorem actual_ordinary_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q a : ℕ)
    (hcap : CandidateCoherence.NoOrdinary S.Adj S.label q a) :
    let T := targetPrefix S F P.strongLower P.strongUpper j x q
    let H := highHeads S F P.strongLower P.strongUpper j x
    T.card ≤  min
      (a-1-((H \ T).filter fun v => (failed S F j x v).card ≤  q).card)
      (a-((H \ T).filter fun v => (failed S F j x v).card ≤  q+1).card) := by
  dsimp only
  have h := ordinary_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strongLower P.strongUpper j x q) (highHeads S F P.strongLower P.strongUpper j x)
    (missing S F j x) q a hcap
    (fun w hw c hc => prefix_partner S F hF i j P x q w hw c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strongLower P.strongUpper j x q)
  simpa only [outsideHigh,guardFailures_eq] using h






theorem residual_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    ResidualCaps.residual S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) (highHeads S F t u j x) w =
      (failed S F j x w).card-((highHeads S F t u j x).filter (S.Adj w)).card := by
  unfold ResidualCaps.residual
  rw [guardFailures_eq]
  rfl

theorem actual_dominator_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (m a : ℕ)
    (hm : m ≤  (highHeads S F P.strongLower P.strongUpper j x).card)
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label m a) :
    (targetPrefix S F P.strongLower P.strongUpper j x 0).card ≤ 
      (targetPrefix S F P.strongLower P.strongUpper j x 0 ∩ highHeads S F P.strongLower P.strongUpper j x).card+(a-1)+
        residualPrefix S F P.strongLower P.strongUpper j x m := by
  have h := dominator_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strongLower P.strongUpper j x 0) (highHeads S F P.strongLower P.strongUpper j x)
    (missing S F j x) (highHeads S F P.strongLower P.strongUpper j x).toList
    (Finset.nodup_toList _) (by simp) m a (by simpa using hm) hcap
    (fun w hw c hc => prefix_partner S F hF i j P x 0 w hw c hc)
    (high_guards_true S F hF i j P x)
    (fun v hv => Nat.eq_zero_of_le_zero (prefix_guard_budget S F P.strongLower P.strongUpper j x 0 v hv))
  have he := funext (residual_eq S F P.strongLower P.strongUpper j x)
  simpa only [he,residualPrefix] using h



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

theorem outside_high_eq
    (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤  3) (tag : V → Fin 11)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 3
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) (q b : ℕ) :
    ((highHeads S F P.strongLower P.strongUpper j x \
      targetPrefix S F P.strongLower P.strongUpper j x q).filter
      fun w => (failed S F j x w).card ≤  b) =
      (highHeads S F P.strongLower P.strongUpper j x).filter fun w =>
        ThreeBoundHighTypes.positivePrefix 3 q (tag w)=false ∧ ThreeBoundHighTypes.budget 3 (tag w) ≤  b := by
  ext w
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  by_cases hh : w ∈ highHeads S F P.strongLower P.strongUpper j x
  · have ht := kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q
    have hc := ThreeBoundHighTypes.ofKind_count 3 (failed S F j x w).card _ _ (tag w)
      (fun b hb => hb.1.2.1) (fun b hb => hb.2.1) (hk w hh)
    simp only [hh,true_and,hc,ht]
    cases ThreeBoundHighTypes.positivePrefix 3 q (tag w) <;> simp
  · simp [hh]




theorem headCount_card (H : Finset V) (tag : V → Fin 11) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount H tag k) : headCount r=H.card := by
  unfold headCount
  simpa only [hx] using sum_typeCounts H tag

theorem lowCount_card (H : Finset V) (tag : V → Fin 11) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount H tag k) (q : ℕ) :
    lowCount r q = (H.filter fun w => ThreeBoundHighTypes.positivePrefix 3 q (tag w)=false ∧ ThreeBoundHighTypes.budget 3 (tag w) ≤  q).card := by
  have he := card_filter_tag H tag (fun k => ThreeBoundHighTypes.positivePrefix 3 q k=false ∧ ThreeBoundHighTypes.budget 3 k ≤  q)
  unfold lowCount
  simp only [hx]
  convert he.symm using 1 <;> congr 1 <;> ext w <;> simp

theorem nextCount_card (H : Finset V) (tag : V → Fin 11) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount H tag k) (q : ℕ) :
    nextCount r q = (H.filter fun w => ThreeBoundHighTypes.positivePrefix 3 q (tag w)=false ∧ ThreeBoundHighTypes.budget 3 (tag w) ≤  q+1).card := by
  have he := card_filter_tag H tag (fun k => ThreeBoundHighTypes.positivePrefix 3 q k=false ∧ ThreeBoundHighTypes.budget 3 k ≤  q+1)
  unfold nextCount
  simp only [hx]
  convert he.symm using 1 <;> congr 1 <;> ext w <;> simp

theorem eligibleCount_card (H : Finset V) (tag : V → Fin 11) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount H tag k) (q : ℕ) :
    eligibleCount r q = (H.filter fun w => ThreeBoundHighTypes.budget 3 (tag w) ≤  q+1).card := by
  have he := card_filter_tag H tag (fun k => ThreeBoundHighTypes.budget 3 k ≤  q+1)
  unfold eligibleCount
  simp only [hx]
  convert he.symm using 1 <;> congr 1 <;> ext w <;> simp

theorem positivePrefix_card (H : Finset V) (tag : V → Fin 11) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount H tag k) (q : ℕ) :
    positivePrefix r q = (H.filter fun w => ThreeBoundHighTypes.positivePrefix 3 q (tag w)=true).card := by
  have he := card_filter_tag H tag (fun k => ThreeBoundHighTypes.positivePrefix 3 q k=true)
  unfold positivePrefix
  simp only [hx]
  convert he.symm using 1 <;> congr 1 <;> ext w <;> simp




end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The exact q3 prefix cap program applied to actual min/max candidates. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundAccounting ThreeBoundNumeric
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem actual_capPrefix (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (input : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤  3) (tag : V → Fin 11)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      ThreeBoundHighTypes.OfKind 3
        (PositiveCandidate S F P.strongLower P.strongUpper j input w)
        (GuardCandidate S F P.strongLower P.strongUpper j input w) (tag w))
    (hc : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      (failed S F j input w).card = ThreeBoundHighTypes.budget 3 (tag w))
    (caps : Caps) (perfect : ℕ) (hcap : CapsSound S.Adj S.label caps perfect) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount (highHeads S F P.strongLower P.strongUpper j input) tag k)
    (hrs : ∀ k : Fin 7, k.val+1 ≤  (highHeads S F P.strongLower P.strongUpper j input).card →
      r (34+k.val)=residualPrefix S F P.strongLower P.strongUpper j input (k.val+1))
    (q : ℕ) (hq : q ≤  3) :
    (targetPrefix S F P.strongLower P.strongUpper j input q).card ≤  capPrefix caps r q := by
  let H := highHeads S F P.strongLower P.strongUpper j input
  let T := targetPrefix S F P.strongLower P.strongUpper j input q
  have hhead : headCount r=H.card := headCount_card H tag r hx
  have hlow : lowCount r q=((H \ T).filter fun w => (failed S F j input w).card ≤  q).card := by
    exact (lowCount_card H tag r hx q).trans
      (congrArg Finset.card (outside_high_eq S F hF i j P input hQ tag hk q q).symm)
  have hnext : nextCount r q=((H \ T).filter fun w => (failed S F j input w).card ≤  q+1).card := by
    exact (nextCount_card H tag r hx q).trans
      (congrArg Finset.card (outside_high_eq S F hF i j P input hQ tag hk q (q+1)).symm)
  have helig : eligibleCount r q=(H.filter fun w => (failed S F j input w).card ≤  q+1).card := by
    refine (eligibleCount_card H tag r hx q).trans ?_
    congr 1
    ext w
    simp only [Finset.mem_filter]
    by_cases hw : w ∈ H
    · simp only [hw,true_and,hc w hw]
    · simp [hw]
  have hpos (b : ℕ) : positivePrefix r b=
      (targetPrefix S F P.strongLower P.strongUpper j input b ∩ H).card :=
    (positivePrefix_card H tag r hx b).trans
      (congrArg Finset.card (prefix_high_eq S F hF i j P input hQ tag hk b).symm)
  apply capPrefix_bound caps r q _ hq
  · rw [hlow,hnext]
    exact actual_ordinary_prefix_cap S hR F hF i j P input q _ (hcap.ordinary q hq)
  · intro hq0 hm
    subst q
    rw [hhead] at hm
    have h := actual_dominator_prefix_cap S hR F hF i j P input 1 (caps.pcross+1) hm hcap.source
    rw [← hpos 0,← hrs ⟨0,by decide⟩ hm] at h
    simpa only [Nat.add_sub_cancel,Fin.val_mk,Nat.add_zero,Nat.zero_add] using h
  · intro hq0 hm
    subst q
    rw [hhead] at hm
    have h := actual_dominator_prefix_cap S hR F hF i j P input 2 (Caps.at caps.zero 2+1) hm hcap.double
    rw [← hpos 0,← hrs ⟨1,by decide⟩ hm] at h
    simpa only [Nat.add_sub_cancel,Fin.val_mk,Nat.reduceAdd] using h
  · intro hq0 hm
    rw [helig] at hm
    rw [hnext]
    exact actual_marked_prefix_cap S F hF i j P input q 1 _ hm
      (by simpa using hcap.markedOne q (by omega) hq)
  · intro hq0 hq2 hm
    rw [helig] at hm
    rw [hnext]
    exact actual_marked_prefix_cap S F hF i j P input q 2 _ hm
      (hcap.markedTwo q (by omega) hq2)
  · intro hq1 hm
    subst q
    rw [hhead] at hm
    have h := actual_zero_marked_prefix_cap S hR F hF i j P input 1 3 _ hm (Or.inl (by omega)) hcap.zeroThree
    rw [← hpos 1,← hrs ⟨2,by decide⟩ hm] at h
    exact h
  · intro hq2 hm
    subst q
    rw [hhead] at hm
    have h := actual_zero_marked_prefix_cap S hR F hF i j P input 2 4 _ hm (Or.inl (by omega)) hcap.zeroFour
    rw [← hpos 2,← hrs ⟨3,by decide⟩ hm] at h
    exact h
  · intro hq3 hm
    subst q
    rw [hhead] at hm
    have h := actual_zero_marked_prefix_cap S hR F hF i j P input 3 5 _ hm (Or.inl (by omega)) hcap.zeroFive
    rw [← hpos 3,← hrs ⟨4,by decide⟩ hm] at h
    exact h
  · intro hq3 hm
    subst q
    rw [hhead] at hm
    have h := actual_zero_marked_prefix_cap S hR F hF i j P input 3 6 _ hm (Or.inr hQ) hcap.zeroSix
    rw [← hpos 3,← hrs ⟨5,by decide⟩ hm] at h
    exact h
  · intro hq3 hm
    subst q
    rw [hhead] at hm
    have h := actual_zero_marked_prefix_cap S hR F hF i j P input 3 7 _ hm (Or.inr hQ) hcap.zeroSeven
    rw [← hpos 3,← hrs ⟨6,by decide⟩ hm] at h
    exact h

end
end ThreeBoundRankNumeric



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
  (input : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (tag : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
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
            j input)
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
            j input w)
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
            j input w)
          (tag w))
  (hc :
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
            j input)
          w →
        @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j input w))
          (Sensitivity213981Formal.ThreeBoundHighTypes.budget
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (tag w)))
  (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (hcap :
    @Sensitivity213981Formal.ThreeBoundRankNumeric.CapsSound V inst_2
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S) caps perfect)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record)
  (hx :
    ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))),
      @Eq.{1} Nat (r (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) k))
        (@Sensitivity213981Formal.ThreeBoundAccounting.typeCount V
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
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
            j input)
          tag k))
  (hrs :
    ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Finset.card.{0} V
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
              j input)) →
        @Eq.{1} Nat
          (r
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
              (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCaps.residualPrefix L I V inst_2 S F
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
            j input
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (q : Nat) (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} V
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.targetPrefix L I V inst_2 S F
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
        j input q))
    (Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix caps r q) := @Sensitivity213981Formal.ThreeBoundRankNumeric.actual_capPrefix
