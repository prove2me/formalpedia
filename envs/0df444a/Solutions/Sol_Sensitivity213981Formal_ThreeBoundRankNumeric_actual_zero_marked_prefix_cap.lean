-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.actual_zero_marked_prefix_cap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:17:13.00154+00:00
-- url     : https://prove2.me/submissions/6d7bd658-fbb2-4597-a704-ecab4f1bccbf

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMarkers_exists_markers_of_sorted_prefix


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











end GuardSemantics
end TournamentHighRows








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
The graded-target to labeling-exclusion bridge.

Targets at different rows may use different lower thresholds. A geometric
one-child candidate has an accepted partner; coloring its row by the other
position makes every label mismatch an actual guard failure. This argument
is independent of fixed versus graded targets and applies to min/max targets.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows

variable {N : ℕ} {V X : Type}























section ActualGuards
variable [Fintype V]

/-- Each label mismatch enters the actual selected-child failure set. -/
theorem mismatch_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b)) (v : V) :
    mismatch R ell T color v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hvw,hlabel⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,hvw,hpartner w hwT (ell v w) hlabel⟩









end ActualGuards
end CandidateCoherence







end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Actual guard augmentation for graded-target candidates.

The optional matching and near-coloring argument is adapted from the accepted
CompactTournament.augment_by_guards proof in the attached Paley11987 source
(prove2.me submission 7f5aa99d-5bc6-4815-915f-ef258368885d). This module specializes
its abstract combinatorics to the actual Boolean selected-child guard sets in
TournamentHighRows and the graded target colors in CandidateCoherence.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GuardAugmentation
open scoped Classical
open Finset MinmaxLocal TournamentHighRows CandidateCoherence
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]











/-- Every abstract augmentation charge is an actual guard failure. The
    disjointness of candidates and high rows prevents double-counting. -/
theorem charges_card_le_actual_failures (R : V → V → Prop)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (C G : Finset V) (hdis : Disjoint C G) (base : V → Bool)
    (hpartner : ∀ w ∈ C, ∀ b : Bool, b ≠ base w → P (children w b))
    (hhigh : ∀ w ∈ G, ∀ b : Bool, P (children w b)) (v : V) :
    (mismatch R ell C base v).card + (outNeighbors R G v).card ≤ 
      (guardFailures R ell P children v).card := by
  have hd : Disjoint (mismatch R ell C base v) (outNeighbors R G v) := by
    apply Finset.disjoint_left.mpr
    intro w hwC hwG
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hwC).1 (Finset.mem_filter.mp hwG).1
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  apply Finset.union_subset
  · exact mismatch_subset_failures R ell P children C base hpartner v
  · exact out_high_subset_failures R ell P children G hhigh v



end
end GuardAugmentation







end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Source, double-dominator, and zero-mismatch residual caps for actual graded
target candidates. The residuals are actual failed guards left after all arcs
inside the full high-row tournament have been charged.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]













theorem mismatch_card_le_residual (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X)
    (A H : Finset V) (hdis : Disjoint A H) (color : V → Bool)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c)) (v : V) :
    (mismatch R ell A color v).card ≤  residual R ell guard children H v := by
  have h := charges_card_le_actual_failures R ell guard children A H hdis color hpartner hhigh v
  unfold residual
  omega

theorem deletedHeads_subset (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : deletedHeads R ell A M color ⊆ A := by
  intro w hw
  obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hw
  exact (Finset.mem_filter.mp hv).1

theorem cleanedHeads_subset (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : cleanedHeads R ell A M color ⊆ A :=
  Finset.sdiff_subset

theorem cleaned_plus_deleted (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) :
    (cleanedHeads R ell A M color).card + (deletedHeads R ell A M color).card = A.card :=
  Finset.card_sdiff_add_card_eq_card (deletedHeads_subset R ell A M color)

theorem marker_clean_mismatch_empty (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) (v : V) (hv : v ∈ M) :
    mismatch R ell (cleanedHeads R ell A M color) color v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwC,hvw,hcolor⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwA,hwD⟩ := Finset.mem_sdiff.mp hwC
  exact hwD (Finset.mem_biUnion.mpr
    ⟨v,hv,Finset.mem_filter.mpr ⟨hwA,hvw,hcolor⟩⟩)







theorem outNeighbors_card_le_pred (R : V → V → Prop) (hR : IsTournament R)
    (M : Finset V) (v : V) (hv : v ∈ M) : (outNeighbors R M v).card ≤  M.card-1 := by
  have hsub : outNeighbors R M v ⊆ M.erase v := by
    intro w hw
    obtain ⟨hwM,hvw⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_erase.mpr
    refine ⟨?_,hwM⟩
    intro he
    subst w
    exact hR.loopless v hvw
  have h := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem hv] at h





end
end ResidualCaps







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



theorem exists_markers_finset (H : Finset V) (res : V → ℕ)
    (k : ℕ) (hk : k ≤  H.card) :
    ∃ M : Finset V, M ⊆ H ∧ M.card = k ∧
      (∑ v ∈ M, res v) = (((H.toList.map res).mergeSort (· ≤  ·)).take k).sum := by
  have hh := exists_markers_of_sorted_prefix H.toList H.nodup_toList res k
    (by simpa using hk)
  simpa using hh



end
end ThreeBoundMarkers




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








theorem residual_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    ResidualCaps.residual S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) (highHeads S F t u j x) w =
      (failed S F j x w).card-((highHeads S F t u j x).filter (S.Adj w)).card := by
  unfold ResidualCaps.residual
  rw [guardFailures_eq]
  rfl





end
end ThreeBoundMinmaxCaps



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Marker deletion caps using the actual mismatches into the target set.
The marker budget is proved from their true guard counts, so the q3
six- and seven-marker refinements require no false size restriction. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankMarkers
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
noncomputable section
variable {V X : Type} [Fintype V] [DecidableEq V]




theorem cleaned_marked_of_marker_budget (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (q : ℕ) (hMB : ∀ v ∈ M, (outNeighbors R M v).card ≤  q+1)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤  q) :
    MarkedGood R ell (cleanedHeads R ell A M color) M q 0 color := by
  let C := cleanedHeads R ell A M color
  have hCA : C ⊆ A := cleanedHeads_subset R ell A M color
  have hzero : ∀ v ∈ M, (mismatch R ell C color v).card = 0 := by
    intro v hv
    rw [marker_clean_mismatch_empty R ell A M color v hv]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (charges_card_le_actual_failures R ell guard children C M (hdis.mono hCA hMH)
      color (fun w hw => hpartner w (hCA hw)) (fun w hw => hhigh w (hMH hw)) v).trans
      (hbudget v (hCA hv))
  · intro v hv
    rw [hzero v hv, Nat.add_zero]
    exact hMB v hv
  · have hz : (∑ v ∈ M, (mismatch R ell C color v).card) = 0 :=
      Finset.sum_eq_zero (fun v hv => hzero v hv)
    exact hz.le


theorem marked_mismatch_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (q m a : ℕ) (hM : M.card = m)
    (hMB : ∀ v ∈ M, (outNeighbors R M v).card ≤  q+1)
    (hcap : MarkedCardBound R ell q m 0 a)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤  q) :
    A.card ≤  a-1 + ∑ v ∈ M, (mismatch R ell A color v).card := by
  let C := cleanedHeads R ell A M color
  have hCA : C ⊆ A := cleanedHeads_subset R ell A M color
  have hg := cleaned_marked_of_marker_budget R hR ell guard children A H M hdis hMH color q
    hMB hpartner hhigh hbudget
  have hC := hcap C M color (hdis.mono hCA hMH) hM hg
  have hsum : (deletedHeads R ell A M color).card ≤  ∑ v ∈ M, (mismatch R ell A color v).card := Finset.card_biUnion_le
  have htotal := cleaned_plus_deleted R ell A M color
  change C.card + (deletedHeads R ell A M color).card = A.card at htotal
  omega

end
end ThreeBoundRankMarkers




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Sorted-residual zero-marker caps, including six and seven markers at q3.
Large marker sets use their actual guard budgets inside the high tournament. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundRankMarkers CandidateCoherence TournamentHighRows
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem high_marker_outdegree (S : Stage L I V)
    (hR : IsTournament S.Adj) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (M : Finset V) (hMH : M ⊆ highHeads S F P.strongLower P.strongUpper j x)
    (q m : ℕ) (hM : M.card=m) (hbudget : m ≤  q+2 ∨ S.tolerance j ≤  q)
    (v : V) (hv : v ∈ M) : (outNeighbors S.Adj M v).card ≤  q+1 := by
  rcases hbudget with hsmall | htol
  · have hh := ResidualCaps.outNeighbors_card_le_pred S.Adj hR M v hv
    rw [hM] at hh
    omega
  · have hsub : outNeighbors S.Adj M v ⊆ failed S F j x v := by
      intro w hw
      obtain ⟨hwM,hvw⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvw,
        high_guards_true S F hF i j P x w (hMH hwM) (S.label v w)⟩
    have hh := Finset.card_le_card hsub
    rcases (Finset.mem_filter.mp (hMH hv)).2 with ⟨b,hb⟩ | ⟨b,hb⟩
    · rw [hb.1.2.1] at hh
      exact hh.trans ((hb.1.1.trans htol).trans (Nat.le_succ _))
    · rw [hb.2.1] at hh
      exact hh.trans (Nat.add_le_add_right (hb.1.trans htol) 1)

theorem actual_zero_marked_prefix_cap (S : Stage L I V)
    (hR : IsTournament S.Adj) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool) (q m a : ℕ)
    (hm : m ≤  (highHeads S F P.strongLower P.strongUpper j x).card)
    (hbudget : m ≤  q+2 ∨ S.tolerance j ≤  q)
    (hcap : ResidualCaps.MarkedCardBound S.Adj S.label q m 0 a) :
    (targetPrefix S F P.strongLower P.strongUpper j x q).card ≤ 
      (targetPrefix S F P.strongLower P.strongUpper j x q ∩
        highHeads S F P.strongLower P.strongUpper j x).card+(a-1)+
          residualPrefix S F P.strongLower P.strongUpper j x m := by
  let H := highHeads S F P.strongLower P.strongUpper j x
  let T := targetPrefix S F P.strongLower P.strongUpper j x q
  let A := T \ H
  let weight := fun v => (failed S F j x v).card-(H.filter (S.Adj v)).card
  obtain ⟨M,hMH,hM,hsum⟩ := ThreeBoundMarkers.exists_markers_finset H weight m hm
  have hdis : Disjoint A H := Finset.disjoint_left.mpr (fun v hv hh => (Finset.mem_sdiff.mp hv).2 hh)
  have hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ missing S F j x w →
      F (S.guard j) (child x w c)=true :=
    fun w hw c hne => prefix_partner S F hF i j P x q w (Finset.mem_sdiff.mp hw).1 c hne
  have hhigh := high_guards_true S F hF i j P x
  have hMB := high_marker_outdegree S hR F hF i j P x M hMH q m hM hbudget
  have hc := marked_mismatch_cap S.Adj hR S.label (fun z => F (S.guard j) z=true)
    (child x) A H M hdis hMH (missing S F j x) q m a hM hMB hcap hpartner hhigh
    (fun w hw => prefix_guard_budget S F P.strongLower P.strongUpper j x q w (Finset.mem_sdiff.mp hw).1)
  have hw : (∑ v ∈ M, (mismatch S.Adj S.label A (missing S F j x) v).card) ≤  ∑ v ∈ M, weight v := by
    apply Finset.sum_le_sum
    intro v _
    have hh := ResidualCaps.mismatch_card_le_residual S.Adj S.label (fun z => F (S.guard j) z=true)
      (child x) A H hdis (missing S F j x) hpartner hhigh v
    rw [residual_eq S F P.strongLower P.strongUpper j x v] at hh
    exact hh
  have hsum' : (∑ v ∈ M, weight v)=residualPrefix S F P.strongLower P.strongUpper j x m := hsum
  have hA := hc.trans (Nat.add_le_add_left hw _)
  rw [hsum'] at hA
  have hpart : A.card+(T ∩ H).card=T.card := Finset.card_sdiff_add_card_inter T H
  change T.card ≤  (T ∩ H).card+(a-1)+_
  omega

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
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (q m a : Nat)
  (hm :
    @LE.le.{0} Nat instLENat m
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
          j x)))
  (hbudget :
    Or
      (@LE.le.{0} Nat instLENat m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j) q))
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.MarkedCardBound V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S) q m
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a),
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
        j x q))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Finset.card.{0} V
          (@Inter.inter.{0} (Finset.{0} V)
            (@Finset.instInter.{0} V fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
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
              j x q)
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
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
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
        j x m)) := @Sensitivity213981Formal.ThreeBoundRankNumeric.actual_zero_marked_prefix_cap
