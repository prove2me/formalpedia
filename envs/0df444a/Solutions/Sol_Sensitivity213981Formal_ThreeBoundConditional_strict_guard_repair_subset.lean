-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.strict_guard_repair_subset
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:56:21.839554+00:00
-- url     : https://prove2.me/submissions/71b0c4db-c52e-45b6-b8aa-4dc1c992312a

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_repair_cases
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_mem_liftBits


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
























































@[simp] theorem ordinary_row_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    ordinaryRowBool S F t g q v x = true ↔ ordinaryRow S F t g q x v := by
  simp [ordinaryRowBool]


















end
end ThreeBoundConditional




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Strict conditional union transfer for actual Boolean rows and parents. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]






















theorem strict_guard_repair_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v w₀ : V)
    (ht : ∀ c : Bool, F t (child x v c)=true)
    (hg : guardFailures S F g x v={w₀}) :
    flipsTo (ordinaryRowBool S F t g 0 v) true x ⊆
      liftBits w₀ (S.label v w₀) (flipsTo (F g) false (child x w₀ (S.label v w₀))) := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (ordinary_row_true S F t g 0 _ v).1 (Finset.mem_filter.mp ha).2
  have hoff : ¬ordinaryRow S F t g 0 x v := by
    intro hv
    have hc := hv.2
    simp [hg] at hc
  rcases strict_repair_cases S F t g x v w c a hoff hon with hh | hh
  · have h := ht c
    rw [hh.2.1] at h
    contradiction
  · obtain ⟨_,hgs,hR,hl,_,hf⟩ := hh
    have hw : w=w₀ := by rw [hg] at hgs; simpa using hgs.symm
    subst w
    subst c
    exact (mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩⟩














end
end ThreeBoundConditional



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (t g : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w₀ : V)
  (ht : ∀ (c : Bool), @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hg :
    @Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_1 S F g x v)
      (@Singleton.singleton.{0, 0} V (Finset.{0} V) (@Finset.instSingleton.{0} V) w₀)),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_1 S F t g
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
      Bool.true x)
    (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V w₀
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst (F g) Bool.false
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
          (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))) := @Sensitivity213981Formal.ThreeBoundConditional.strict_guard_repair_subset
