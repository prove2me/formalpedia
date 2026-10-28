-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxCaps.actual_marked_prefix_cap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:23:12.346018+00:00
-- url     : https://prove2.me/submissions/86d893df-0dab-4707-ae83-82b56572a7d0

import Definitions.Def_Sensitivity213981Formal_ActualPrefixCaps
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
import Theorems.Thm_Sensitivity213981Formal_MarkedCandidateCaps_exists_markers_outside_first


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
/-
Unrestricted marked prefix caps and the outside-first marker choice used in
the exact q2 recurrence. These theorems refer to actual selected-child guards.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MarkedCandidateCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]

theorem markedGood_of_actual_guards (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (A M : Finset V)
    (hdis : Disjoint A M) (q : ℕ) (color : V → Bool)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ M, ∀ c : Bool, guard (children w c))
    (hA : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤  q)
    (hM : ∀ v ∈ M, (guardFailures R ell guard children v).card ≤  q+1) :
    ResidualCaps.MarkedGood R ell A M q (M.card*(q+1)) color := by
  have hcharge (v : V) :=
    charges_card_le_actual_failures R ell guard children A M hdis color hpartner hhigh v
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (hcharge v).trans (hA v hv)
  · intro v hv
    rw [Nat.add_comm]
    exact (hcharge v).trans (hM v hv)
  · calc
      (∑ v ∈ M, (mismatch R ell A color v).card) ≤  ∑ v ∈ M, (q+1) := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.card_le_card
          (mismatch_subset_failures R ell guard children A color hpartner v)).trans (hM v hv)
      _ = M.card*(q+1) := by simp

/-- Markers that already belong to the target prefix are removed before the
    marked exclusion is applied, and counted back exactly once. -/
theorem actual_marked_prefix_cap (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (T M : Finset V)
    (q m a : ℕ) (hMcard : M.card = m)
    (hcap : MarkedCardBound R ell q m (m*(q+1)) a) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ M, ∀ c : Bool, guard (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell guard children v).card ≤  q)
    (hM : ∀ v ∈ M, (guardFailures R ell guard children v).card ≤  q+1) :
    T.card ≤  a-1 + (T ∩ M).card := by
  let A := T \ M
  have hAT : A ⊆ T := Finset.sdiff_subset
  have hdis : Disjoint A M := Finset.sdiff_disjoint
  have hg := markedGood_of_actual_guards R ell guard children A M hdis q color
    (fun w hw => hpartner w (hAT hw)) hhigh (fun v hv => hT v (hAT hv)) hM
  rw [hMcard] at hg
  have hc := hcap A M color hdis hMcard hg
  have hsum := Finset.card_sdiff_add_card_inter T M
  change A.card + (T ∩ M).card = T.card at hsum
  omega



/-- The configured one-marker and two-marker correction is justified for every graded
    target prefix, including positive high rows at higher tiers. -/
theorem actual_marked_outside_first_cap (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (T E : Finset V)
    (q m a : ℕ) (hm : m ≤  E.card)
    (hcap : MarkedCardBound R ell q m (m*(q+1)) a) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ E, ∀ c : Bool, guard (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell guard children v).card ≤  q)
    (hE : ∀ v ∈ E, (guardFailures R ell guard children v).card ≤  q+1) :
    T.card ≤  a-1 + (m - (E \ T).card) := by
  obtain ⟨M,hME,hMc,hint⟩ := exists_markers_outside_first T E m hm
  have h := actual_marked_prefix_cap R ell guard children T M q m a hMc hcap color
    hpartner (fun w hw => hhigh w (hME hw)) hT (fun v hv => hE v (hME hv))
  exact h.trans (Nat.add_le_add_left hint (a-1))

end
end MarkedCandidateCaps






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







theorem marked_prefix_cap (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (T H : Finset V)
    (color : V → Bool) (q m a : ℕ)
    (hm : m ≤  (eligibleHigh R ell P children H q).card)
    (hcap : MarkedCardBound R ell q m (m*(q+1)) a)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → P (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤  q) :
    T.card ≤  a-1 + (m-(outsideHigh R ell P children H T (q+1)).card) := by
  have he : eligibleHigh R ell P children H q \ T =
      outsideHigh R ell P children H T (q+1) := by
    ext v
    simp only [eligibleHigh,outsideHigh,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have h := actual_marked_outside_first_cap R ell P children T
    (eligibleHigh R ell P children H q) q m a hm hcap color hpartner
    (fun w hw => hhigh w (Finset.mem_filter.mp hw).1) hT
    (fun _ hv => (Finset.mem_filter.mp hv).2)
  simpa only [he] using h





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



theorem actual_marked_prefix_cap (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q m a : ℕ)
    (hm : m ≤  ((highHeads S F P.strongLower P.strongUpper j x).filter fun v => (failed S F j x v).card ≤  q+1).card)
    (hcap : ResidualCaps.MarkedCardBound S.Adj S.label q m (m*(q+1)) a) :
    let T := targetPrefix S F P.strongLower P.strongUpper j x q
    let H := highHeads S F P.strongLower P.strongUpper j x
    T.card ≤  a-1+(m-((H \ T).filter fun v => (failed S F j x v).card ≤  q+1).card) := by
  dsimp only
  have hm' : m ≤  (eligibleHigh S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) (highHeads S F P.strongLower P.strongUpper j x) q).card := by
    simpa only [eligibleHigh,guardFailures_eq] using hm
  have h := marked_prefix_cap S.Adj S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strongLower P.strongUpper j x q) (highHeads S F P.strongLower P.strongUpper j x)
    (missing S F j x) q m a hm' hcap
    (fun w hw c hc => prefix_partner S F hF i j P x q w hw c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strongLower P.strongUpper j x q)
  simpa only [outsideHigh,guardFailures_eq] using h










end
end ThreeBoundMinmaxCaps



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
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
        (@Finset.filter.{0} V
          (fun (v : V) =>
            @LE.le.{0} Nat instLENat
              (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x v))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun (a : V) =>
            Nat.decLe (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x a))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
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
            j x))))
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.MarkedCardBound V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S) q m
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      a),
  have T : Finset.{0} V :=
    @Sensitivity213981Formal.ThreeBoundMinmaxCandidates.targetPrefix L I V inst_2 S F
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
      j x q;
  have H : Finset.{0} V :=
    @Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
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
      j x;
  @LE.le.{0} Nat instLENat (@Finset.card.{0} V T)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m
        (@Finset.card.{0} V
          (@Finset.filter.{0} V
            (fun (v : V) =>
              @LE.le.{0} Nat instLENat
                (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x v))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (fun (a : V) =>
              Nat.decLe (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x a))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@SDiff.sdiff.{0} (Finset.{0} V)
              (@Finset.instSDiff.{0} V fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b)) H T))))) := @Sensitivity213981Formal.ThreeBoundMinmaxCaps.actual_marked_prefix_cap
