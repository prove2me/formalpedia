-- Prove2me | solution 1 for ThreeBoundConditional.ordinaryGuardBits_card_special
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:40:56.203844+00:00
-- url     : https://prove2.me/submissions/3064f546-5636-409b-9b0a-4e3939b8ac29

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
/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]













@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]














@[simp] theorem mem_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passingGuards S F g x v ↔
      S.Adj v w ∧ F g (child x w (S.label v w)) = false := by
  simp only [passingGuards, outgoing, guardFailures, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases F g (child x w (S.label v w)) <;> simp

theorem card_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (passingGuards S F g x v).card =
      (outgoing S v).card - (guardFailures S F g x v).card := by
  apply Finset.card_sdiff_of_subset
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_guardFailures S F g x v w).1 hw |>.1⟩












































end
end ThreeBoundConditional




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

theorem solution (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj gk : L) (x : ((V × Bool) × I) → Bool) (v w : V) (a p : ℕ)
    (ha : ABound F gj gi a) (hp : PBound F gk gj gi p)
    (hw : w ∈ passingGuards S F gj x v)
    (hk : F gk (child x w (S.label v w)) = true) :
    (ordinaryGuardBits S F gi gj x v).card ≤
      ((outgoing S v).card - (guardFailures S F gj x v).card - 1)*a+p := by
  have hsplit : passingGuards S F gj x v =
      insert w ((passingGuards S F gj x v).erase w) := (Finset.insert_erase hw).symm
  unfold ordinaryGuardBits
  rw [hsplit,Finset.biUnion_insert]
  calc
    _ ≤ (liftBits w (S.label v w)
      (flipsTo (F gi) true (child x w (S.label v w)))).card +
      (((passingGuards S F gj x v).erase w).biUnion fun z =>
        liftBits z (S.label v z) (flipsTo (F gi) true (child x z (S.label v z)))).card :=
      Finset.card_union_le _ _
    _ ≤ p + (((passingGuards S F gj x v).erase w).card*a) := by
      apply Nat.add_le_add
      · rw [card_liftBits]
        exact hp _ hk ((mem_passingGuards S F gj x v w).1 hw).2
      · apply Finset.card_biUnion_le.trans
        calc
          _ ≤ ∑ _z ∈ (passingGuards S F gj x v).erase w, a := by
            apply Finset.sum_le_sum
            intro z hz
            rw [card_liftBits]
            exact ha _ ((mem_passingGuards S F gj x v z).1 (Finset.mem_of_mem_erase hz)).2
          _ = _ := by simp
    _ = _ := by rw [Finset.card_erase_of_mem hw,card_passingGuards]; omega
end
