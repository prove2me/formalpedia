-- Prove2me | solution 1 for ThreeBoundConditionalNumeric.matched_same_parent
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:45:51.428287+00:00
-- url     : https://prove2.me/submissions/0fe45006-2e95-4221-8593-9d2cbee7d37f

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
import Definitions.Def_Sensitivity213303_ArchivedOrdinaryDefinitions
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_Endpoint40Recipes
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCostExpressions
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_Sensitivity213303_MinMaxNesting
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_OrdinaryParentBridge
import Definitions.Def_Sensitivity213303_Paley10007
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_Selected10007
import Definitions.Def_Sensitivity213303_SelectedBoolCaps
import Definitions.Def_Sensitivity213303_SelectedOrdinaryCaps
import Definitions.Def_Sensitivity213303_StrictPositive
import Definitions.Def_Sensitivity213303_StrictUnion
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundConditional
end ThreeBoundConditional
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
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
namespace OAI.Paper320
end OAI.Paper320
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤ S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end

section
/- Semantic interpretation of numeric entries, ordinary components and raw B. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]









theorem same_spec (e f : Entry) (he : e.same f=true) :
    e.tolerance=f.tolerance ∧ e.guard=f.guard ∧
      ∀ d, d ≤ e.tolerance → e.threshold d=f.threshold d := by
  simp only [Entry.same,Bool.decide_and,Bool.and_eq_true,decide_eq_true_eq] at he
  rcases he with ⟨hq,hg,ht⟩
  refine ⟨hq,hg,?_⟩
  intro d hd
  have hh := List.all_eq_true.mp ht d (List.mem_range.mpr (by omega))
  simpa only [beq_iff_eq] using hh













end
end ThreeBoundConditionalNumeric




end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThreeBoundConditionalNumeric
end ThreeBoundConditionalNumeric
open ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem solution (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (i j : Fin n)
    (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (hs : a.same c=true) : parent S F i=parent S F j := by
  obtain ⟨hq,hg,ht⟩ := same_spec a c hs
  have hq' : S.tolerance i=S.tolerance j := by rw [hm.weakTolerance,hm.strongTolerance,hq]
  have hg' : S.guard i=S.guard j := Fin.ext (by rw [hm.weakGuard,hm.strongGuard,hg])
  have ht' (d : ℕ) (hd : d ≤ S.tolerance i) : P.weak d=P.strong d := by
    apply Fin.ext
    rw [hm.weakThreshold,hm.strongThreshold]
    exact ht d (by simpa only [hm.weakTolerance] using hd)
  funext x
  have hf (w : V) : failed S F i x w=failed S F j x w := by simp only [failed,hg']
  have hi : parent S F i x=true ↔ parent S F j x=true := by
    rw [parent_true_iff,parent_true_iff]
    constructor
    · rintro ⟨w,hc,hh⟩
      refine ⟨w,by simpa only [← hf,← hq'] using hc,?_⟩
      rw [P.strongDef,← hf,← ht' _ hc,← P.weakDef]
      exact hh
    · rintro ⟨w,hc,hh⟩
      have hc' : (failed S F i x w).card ≤ S.tolerance i := by simpa only [hf,hq'] using hc
      refine ⟨w,hc',?_⟩
      rw [P.weakDef,ht' _ hc',hf,← P.strongDef]
      exact hh
  cases h₁ : parent S F i x <;> cases h₂ : parent S F j x <;> simp_all
end
