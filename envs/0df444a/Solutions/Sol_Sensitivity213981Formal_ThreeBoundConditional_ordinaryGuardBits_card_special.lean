-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits_card_special
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:33:44.422604+00:00
-- url     : https://prove2.me/submissions/9d5bdbfd-6dc7-4826-a22d-2ee31d88435a

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





theorem ordinaryGuardBits_card_special (S : Stage L I V) (F : L → (I → Bool) → Bool)
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
    _ ≤  (liftBits w (S.label v w)
      (flipsTo (F gi) true (child x w (S.label v w)))).card +
      (((passingGuards S F gj x v).erase w).biUnion fun z =>
        liftBits z (S.label v z) (flipsTo (F gi) true (child x z (S.label v z)))).card :=
      Finset.card_union_le _ _
    _ ≤  p + (((passingGuards S F gj x v).erase w).card*a) := by
      apply Nat.add_le_add
      · rw [card_liftBits]
        exact hp _ hk ((mem_passingGuards S F gj x v w).1 hw).2
      · apply Finset.card_biUnion_le.trans
        calc
          _ ≤  ∑ _z ∈ (passingGuards S F gj x v).erase w, a := by
            apply Finset.sum_le_sum
            intro z hz
            rw [card_liftBits]
            exact ha _ ((mem_passingGuards S F gj x v z).1 (Finset.mem_of_mem_erase hz)).2
          _ = _ := by simp
    _ = _ := by rw [Finset.card_erase_of_mem hw,card_passingGuards]; omega






































end
end ThreeBoundConditional




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (gi gj gk : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (a p : Nat)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst F gj gi a)
  (hp : @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst F gk gj gi p)
  (hw :
    @Membership.mem.{0, 0} V (Finset.{0} V)
      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
      (@Sensitivity213981Formal.ThreeBoundConditional.passingGuards L I V inst_1 S F gj x v) w)
  (hk :
    @Eq.{1} Bool
      (F gk
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w
          (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w)))
      Bool.true),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits L I V inst inst_1 S F gi gj x v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_1 S v))
            (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_1 S F gj x v)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        a)
      p) := @Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits_card_special
