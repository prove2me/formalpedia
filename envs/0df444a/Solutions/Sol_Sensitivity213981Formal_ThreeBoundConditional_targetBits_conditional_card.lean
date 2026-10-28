-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.targetBits_conditional_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:33:11.085768+00:00
-- url     : https://prove2.me/submissions/bb8bdfb7-261f-40ba-a979-36b7526cb2e2

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum


namespace Sensitivity213981Formal
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
end Sensitivity213981Formal

namespace Sensitivity213981Formal
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























/-- The two actual target children contribute the refined conditional cost. -/
theorem targetBits_conditional_card (F : L → (I → Bool) → Bool)
    (ti tj tk : L) (x : ((V × Bool) × I) → Bool) (v : V) (m b : ℕ)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b)
    (ht : ∀ c : Bool, F tj (child x v c) = true)
    (hmiss : ∃ c : Bool, F tk (child x v c) = false) :
    (targetBits F ti x v).card ≤  max (2*m) (m+b) := by
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
end ThreeBoundConditional




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [Fintype.{0} V] (F : L → (I → Bool) → Bool) (ti tj tk : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (m b : Nat)
  (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst F ti tj tk m)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst F ti tk b)
  (ht : ∀ (c : Bool), @Eq.{1} Bool (F tj (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hmiss :
    @Exists.{1} Bool fun (c : Bool) =>
      @Eq.{1} Bool (F tk (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundPositive.targetBits L I V inst F ti x v))
    (@Max.max.{0} Nat Nat.instMax
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m b)) := @Sensitivity213981Formal.ThreeBoundConditional.targetBits_conditional_card
