-- Prove2me | solution 1 for ThreeBoundActualKindFilters.kind_positive_only
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:44:20.651075+00:00
-- url     : https://prove2.me/submissions/0d03f780-0b2c-4d3d-8851-3a83e1baf6e4

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
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
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
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
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundAllKindHeadCosts
end ThreeBoundAllKindHeadCosts
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







end
end ThreeBoundAllKindHeadCosts



end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundActualKindFilters
end ThreeBoundActualKindFilters
open ThreeBoundActualKindFilters
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem solution
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (t : ℕ → Fin n) (j : Fin n) (x : ((V × Bool) × I) → Bool) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind)
    (hp : kind.val ≤ 2) :
    targetAt S F t j x w ∧ ¬ guardAt S F t j x w ∧ (failed S F j x w).card = kind.val := by
  fin_cases kind <;> simp only [Q2CandidateTypes.OfKind] at hk
  all_goals norm_num only at hp
  · have hc := hk.1.2.1
    refine ⟨target_of_positive S F t j x w 0 hk,?_,hc⟩
    rintro ⟨b,hb⟩
    have hbc := hb.2.1
    omega
  · have hc := hk.1.1.2.1
    refine ⟨target_of_positive S F t j x w 1 hk.1,?_,hc⟩
    rintro ⟨b,hb⟩
    have hbc := hb.2.1
    have he : b = 0 := by omega
    exact hk.2 (he ▸ hb)
  · have hc := hk.1.1.2.1
    refine ⟨target_of_positive S F t j x w 2 hk.1,?_,hc⟩
    rintro ⟨b,hb⟩
    have hbc := hb.2.1
    have he : b = 1 := by omega
    exact hk.2 (he ▸ hb)
end
