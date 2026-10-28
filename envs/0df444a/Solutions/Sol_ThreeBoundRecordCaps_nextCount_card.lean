-- Prove2me | solution 1 for ThreeBoundRecordCaps.nextCount_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:44:45.719505+00:00
-- url     : https://prove2.me/submissions/69837f96-bb02-4632-bb3f-2d86af3d1537

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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_ActualTargetAccounting
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_CapAlgorithm
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

namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace ThreeBoundAccounting
end ThreeBoundAccounting
namespace ThreeBoundCapAlgorithm
end ThreeBoundCapAlgorithm
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundTypeCounts
end ThreeBoundTypeCounts
namespace ThreeBoundAccounting
end ThreeBoundAccounting
section
/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
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

section
/- Numerical prefix-cap composition, separated from its actual candidate
proofs. Each premise is one of the independently established labeling caps. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundCapAlgorithm
open ThreeBoundNumeric
open scoped BigOperators Classical









theorem sum_filterMap_eight (x : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((List.range 8).filterMap fun k => if p k then some (x k) else none).sum =
      ∑ k : Fin 8, if p k.val then x k.val else 0 := by
  simp only [List.range_succ,List.range_zero,List.filterMap_append,List.filterMap_cons,
    List.filterMap_nil,List.sum_append,List.sum_cons,List.sum_nil,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,Fin.val_one]
  split_ifs <;> simp_all <;> omega

end ThreeBoundCapAlgorithm



end

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







end
end ThreeBoundTypeCounts

end

section
/- The numerical type-count combinations are exact cardinalities of actual
candidate prefixes and eligible marker sets. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundRecordCaps
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundAccounting ThreeBoundTypeCounts
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V]

theorem kindBudget_eq (k : Fin 8) : kindBudget k.val = ThreeBoundQ2.budget k := by
  fin_cases k <;> rfl

theorem positiveInside_eq (k : Fin 8) (q : ℕ) :
    positiveInside k.val q = ThreeBoundQ2.positivePrefix q k := by
  fin_cases k <;> simp [positiveInside,ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel]











end
end ThreeBoundRecordCaps



end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThreeBoundRecordCaps
end ThreeBoundRecordCaps
open ThreeBoundRecordCaps
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundAccounting ThreeBoundTypeCounts
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem solution (H : Finset V) (tag : V → Fin 8) (x : Q2Record)
    (hx : ∀ k : Fin 8, x k.val = typeCount H tag k) (q : ℕ) :
    nextCount x q = (H.filter fun w =>
      ThreeBoundQ2.positivePrefix q (tag w) = false ∧ ThreeBoundQ2.budget (tag w) ≤ q+1).card := by
  have he := card_filter_tag H tag (fun k =>
    ThreeBoundQ2.positivePrefix q k = false ∧ ThreeBoundQ2.budget k ≤ q+1)
  trans ∑ k : Fin 8, if ThreeBoundQ2.positivePrefix q k = false ∧
      ThreeBoundQ2.budget k ≤ q+1 then typeCount H tag k else 0
  · unfold nextCount
    rw [sum_filterMap_eight]
    apply Finset.sum_congr rfl
    intro k _
    simp only [positiveInside_eq,kindBudget_eq,hx]
    cases ThreeBoundQ2.positivePrefix q k <;> simp
  · convert he.symm using 1 <;> congr 1 <;> ext a <;> simp
end
