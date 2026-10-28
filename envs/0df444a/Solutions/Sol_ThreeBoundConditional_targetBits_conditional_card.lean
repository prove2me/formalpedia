-- Prove2me | solution 1 for ThreeBoundConditional.targetBits_conditional_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:41:04.853313+00:00
-- url     : https://prove2.me/submissions/4c1bfbda-644e-41b3-bcc1-3e107b6bb654

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
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





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _

























end
end ThreeBoundPositive






end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

/-- The two actual target children contribute the refined conditional cost. -/
theorem solution (F : L → (I → Bool) → Bool)
    (ti tj tk : L) (x : ((V × Bool) × I) → Bool) (v : V) (m b : ℕ)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b)
    (ht : ∀ c : Bool, F tj (child x v c) = true)
    (hmiss : ∃ c : Bool, F tk (child x v c) = false) :
    (targetBits F ti x v).card ≤ max (2*m) (m+b) := by
  have hc : (targetBits F ti x v).card ≤
      (flipsTo (F ti) false (child x v false)).card +
      (flipsTo (F ti) false (child x v true)).card := by
    simpa only [targetBits,card_liftBits] using Finset.card_union_le
      (liftBits v false (flipsTo (F ti) false (child x v false)))
      (liftBits v true (flipsTo (F ti) false (child x v true)))
  cases hf : F tk (child x v false) <;> cases htr : F tk (child x v true)
  · exact hc.trans ((Nat.add_le_add (hm _ (ht false) hf) (hm _ (ht true) htr)).trans
      (by omega))
  · exact hc.trans ((Nat.add_le_add (hm _ (ht false) hf) (hb _ htr)).trans
      (le_max_right _ _))
  · exact hc.trans ((Nat.add_le_add (hb _ hf) (hm _ (ht true) htr)).trans (by omega))
  · obtain ⟨c,hc⟩ := hmiss
    cases c <;> simp_all
end
