-- Prove2me | solution 1 for ThreeBoundTagPrefixes.kind_target_prefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:45:50.835687+00:00
-- url     : https://prove2.me/submissions/906e7449-6d9b-4795-823d-cfdc12fb4c67

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_ActualTargetAccounting
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCostExpressions
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundHeadExpressions
end ThreeBoundHeadExpressions
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace TournamentHighRows
end TournamentHighRows
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundActualTargets
end ThreeBoundActualTargets
namespace ThreeBoundAllKindHeadCosts
end ThreeBoundAllKindHeadCosts
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
section
/-
Exact eight-type decomposition for equal-target graded rows through tolerance 2.

The predicates below refer to the actual child truth values and actual failed
guard count. The classification does not assume a sensitivity bound. It can be
instantiated with target b z := F (threshold b) z, and guard := F g.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Q2CandidateTypes
open scoped Classical
open TournamentHighRows

variable {X V : Type}





















theorem ofKind_high (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) (k : Fin 8)
    (hk : OfKind guard target Q d x y k) : High guard target Q d x y := by
  fin_cases k <;> simp only [OfKind] at hk
  · exact Or.inl ⟨0,hk⟩
  · exact Or.inl ⟨1,hk.1⟩
  · exact Or.inl ⟨2,hk.1⟩
  · exact Or.inr ⟨0,hk.1⟩
  · exact Or.inr ⟨1,hk.1⟩
  · exact Or.inr ⟨2,hk⟩
  · exact Or.inl ⟨1,hk.1⟩
  · exact Or.inl ⟨2,hk.1⟩







/-- Every high candidate has both actual guard predicates true. -/
theorem high_guard_true (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (hh : High guard target Q d x y) : guard x ∧ guard y := by
  rcases hh with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact hb.2
  · exact ⟨hgt b hb.1 x hb.2.2.1,hgt b hb.1 y hb.2.2.2⟩







section ActualRows
variable [Fintype V]











end ActualRows
end Q2CandidateTypes









end

section
/- Exact head-cost formulas instantiated from actual graded candidate states. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundActualHeadCosts
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]
variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

theorem high_guards_true (w : V) (hw : w ∈ highHeads S F P.strong j x) (c : Bool) :
    F (S.guard j) (child x w c) = true := by
  have hh := Q2CandidateTypes.high_guard_true (fun z => F (S.guard j) z = true)
    (fun b z => F (P.strong b) z = true) (S.tolerance j) (failed S F j x w).card
    (child x w false) (child x w true)
    (fun b hb z hz => hF _ _ (P.guardTarget b hb) z hz) (Finset.mem_filter.mp hw).2
  cases c
  · exact hh.1
  · exact hh.2



























end
end ThreeBoundActualHeadCosts







end

section
/- The eight actual q2 types all satisfy the exact symbolic head cost. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundAllKindHeadCosts
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem target_of_positive
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (t : ℕ → Fin n) (j : Fin n) (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ)
    (hp : Q2CandidateTypes.PositiveCandidate (fun z => F (S.guard j) z = true)
      (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card b
      (child x w false) (child x w true)) : targetAt S F t j x w := by
  have he := hp.1.2.1
  simpa only [targetAt,he] using hp.1

theorem positive_of_target_high
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool) (w : V)
    (hH : w ∈ highHeads S F P.strong j x) (ht : targetAt S F P.strong j x w) :
    Q2CandidateTypes.PositiveCandidate (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (failed S F j x w).card (child x w false) (child x w true) :=
  ⟨ht,high_guards_true S F hF i j P x w hH false,high_guards_true S F hF i j P x w hH true⟩





end
end ThreeBoundAllKindHeadCosts



end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThreeBoundTagPrefixes
end ThreeBoundTagPrefixes
open ThreeBoundTagPrefixes
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundAllKindHeadCosts
open ThreeBoundActualTargets
open scoped Classical BigOperators
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem solution
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind) (q : ℕ) :
    w ∈ targetPrefix S F P.strong j x q ↔ ThreeBoundQ2.positivePrefix q kind = true := by
  have hhigh := Q2CandidateTypes.ofKind_high (fun z => F (S.guard j) z = true)
    (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
    (child x w false) (child x w true) kind hk
  have hH : w ∈ highHeads S F P.strong j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩
  have htP := fun b hp => target_of_positive S F P.strong j x w b hp
  have hpT := fun ht => positive_of_target_high S F hF i j P x w hH ht
  simp only [targetPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  fin_cases kind <;> simp only [Q2CandidateTypes.OfKind] at hk
  · have ht := htP 0 hk
    have hc := hk.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have ht := htP 1 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have ht := htP 2 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have hc := hk.1.2.1
    have hn : ¬ targetAt S F P.strong j x w := by
      intro ht
      apply hk.2
      simpa only [hc] using hpT ht
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,hn]
  · have hc := hk.1.2.1
    have hn : ¬ targetAt S F P.strong j x w := by
      intro ht
      apply hk.2
      simpa only [hc] using hpT ht
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,hn]
  · have hc := hk.2.1
    have hn : ¬ targetAt S F P.strong j x w := by
      intro ht
      have hh := ht.1
      omega
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,hn]
  · have ht := htP 1 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
  · have ht := htP 2 hk.1
    have hc := hk.1.1.2.1
    simp [ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,ht,hc]
end
