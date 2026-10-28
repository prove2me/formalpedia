-- Prove2me | solution 1 for ThreeBoundActualHeadCosts.negative_guard_false
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:43:48.007945+00:00
-- url     : https://prove2.me/submissions/7f0608e1-b383-4575-bd4b-40553b75b6bf

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
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
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
section
/- Actual upward flips grouped into negative targets, high heads and external
   failed-guard arcs. Internal arcs are deduplicated by their selected child. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCover
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundHeadCharge
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





























theorem target_missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V)
    (hc : targetAt S F t l x w) :
    F (t (failed S F l x w).card) (child x w (missing S F t l x w)) = false ∧
    F (t (failed S F l x w).card) (child x w (!(missing S F t l x w))) = true := by
  rcases hc.2.2 with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simp [missing,h0,Bool.eq_false_iff.mpr h0,h1]
  · simp [missing,h0,Bool.eq_false_iff.mpr h1]





end
end ThreeBoundGradedCover




end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
open ThreeBoundActualHeadCosts
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover
open scoped Classical BigOperators
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]
variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

theorem solution (w : V) (hw : w ∈ negativeTargets S F P.strong j x) :
    F (S.guard j) (child x w (missing S F P.strong j x w)) = false := by
  rcases (Finset.mem_filter.mp hw).2 with ⟨ht,hn⟩
  have hpartner := (target_missing S F P.strong j x w ht).2
  have hpg := hF _ _ (P.guardTarget _ ht.1) _ hpartner
  cases hg : F (S.guard j) (child x w (missing S F P.strong j x w)) with
  | false => rfl
  | true =>
      apply False.elim
      apply hn
      left
      refine ⟨(failed S F j x w).card,ht,?_⟩
      cases hm : missing S F P.strong j x w <;> simp_all
end
