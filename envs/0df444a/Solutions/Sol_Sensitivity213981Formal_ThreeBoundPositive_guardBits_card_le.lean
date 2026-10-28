-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundPositive.guardBits_card_le
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:25:44.345991+00:00
-- url     : https://prove2.me/submissions/b6b5e2d4-de69-48e7-91e3-44c4cf36505b

import Definitions.Def_Sensitivity213981Formal_Namespaces
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





@[simp] theorem mem_passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passing S F j x v ↔
      S.Adj v w ∧ F (S.guard j) (child x w (S.label v w)) = false := by
  simp only [passing, outgoing, failed, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases F (S.guard j) (child x w (S.label v w)) <;> simp

theorem card_passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    (passing S F j x v).card = (outgoing S v).card - (failed S F j x v).card := by
  apply Finset.card_sdiff_of_subset
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.1⟩







theorem guardBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (v : V) (a : ℕ)
    (ha : ABound F (S.guard j) (S.guard i) a) :
    (guardBits S F i j x v).card ≤ 
      ((outgoing S v).card - (failed S F j x v).card)*a := by
  unfold guardBits
  calc
    _ ≤  ∑ w ∈ passing S F j x v,
        (liftBits w (S.label v w)
          (flipsTo (F (S.guard i)) true (child x w (S.label v w)))).card :=
      Finset.card_biUnion_le
    _ ≤  ∑ _w ∈ passing S F j x v, a := by
      apply Finset.sum_le_sum
      intro w hw
      rw [card_liftBits]
      exact ha _ ((mem_passing S F j x v w).mp hw).2
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, card_passing]









end
end ThreeBoundPositive






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [Preorder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (i j : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (a : Nat)
  (ha :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) a),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundPositive.guardBits L I V inst inst_1 S F i j x v))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_1 S v))
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_1 S F j x v)))
      a) := @Sensitivity213981Formal.ThreeBoundPositive.guardBits_card_le
