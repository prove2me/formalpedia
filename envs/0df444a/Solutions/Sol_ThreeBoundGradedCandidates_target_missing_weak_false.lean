-- Prove2me | solution 1 for ThreeBoundGradedCandidates.target_missing_weak_false
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:42:28.875431+00:00
-- url     : https://prove2.me/submissions/222def2c-418c-4fd8-8fd8-88b41ba5f0dc

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
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundRepair
end ThreeBoundRepair
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
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
/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]









/-- A row survives whenever both children reach a safe target at an upper guard count. -/
theorem parent_true_of_count_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : L → ℕ → L) (l : L)
    (ht : Monotone (t l))
    (hgraded : ∀ d u z, S.target l d u z = (F (t l d) u && F (t l d) z))
    (x : ((V × Bool) × I) → Bool) (v : V) (d : ℕ)
    (hdQ : d ≤ S.tolerance l) (hcount : (failed S F l x v).card ≤ d)
    (hx : F (t l d) (child x v false) = true)
    (hy : F (t l d) (child x v true) = true) : parent S F l x = true := by
  apply (parent_true_iff S F l x).2
  refine ⟨v, hcount.trans hdQ, ?_⟩
  rw [hgraded]
  simp only [hF _ _ (ht hcount) _ hx, hF _ _ (ht hcount) _ hy, Bool.and_self]





































end
end ThreeBoundPositive






end

section
/- Actual weak rejection constraints for the q2 head-cost formulas. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

theorem failed_weak_subset (v : V) : failed S F i x v ⊆ failed S F j x v := by
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨_,hR,htrue⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,hF _ _ P.guards _ htrue⟩















end
end ThreeBoundGradedCandidates






end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
open ThreeBoundGradedCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open scoped Classical
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]
variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

/-- At an actual target candidate, its missing child fails the weak same-tier
    target. Otherwise the weak row would already accept at its lower count. -/
theorem solution (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (c : Bool) (hb : b ≤ S.tolerance j)
    (hc : (failed S F j x v).card = b)
    (hpartner : F (P.strong b) (child x v (!c)) = true) :
    F (P.weak b) (child x v c) = false := by
  cases hmissing : F (P.weak b) (child x v c) with
  | false => rfl
  | true =>
      have hcnt : (failed S F i x v).card ≤ b := by
        rw [← hc]
        exact Finset.card_le_card (failed_weak_subset S F hF i j P x v)
      have hp := hF _ _ (P.targets b hb) _ hpartner
      have hboth : ∀ e, F (P.weak b) (child x v e) = true := by
        cases c <;> intro e <;> cases e <;> assumption
      have he := parent_true_of_count_bound S F hF (fun _ => P.weak) i P.weakMono
        P.weakDef x v b (hb.trans P.tolerances) hcnt (hboth false) (hboth true)
      rw [hoff] at he
      contradiction
end
