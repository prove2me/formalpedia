-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundPositive.mem_liftBits
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:28:01.651385+00:00
-- url     : https://prove2.me/submissions/a5e12afa-8eba-46ca-8cc6-c93a27a1acdf

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



















@[simp] theorem mem_liftBits (v w : V) (c e : Bool) (a : I) (s : Finset I) :
    ((w,e),a) ∈ liftBits v c s ↔ w = v ∧ e = c ∧ a ∈ s := by
  unfold liftBits
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    change ((v,c),b) = ((w,e),a) at he
    have hvw := congrArg (fun p => p.1.1) he
    have hce := congrArg (fun p => p.1.2) he
    have hba : b = a := congrArg Prod.snd he
    exact ⟨hvw.symm,hce.symm,hba ▸ hb⟩
  · rintro ⟨rfl,rfl,ha⟩
    exact ⟨a,ha,rfl⟩



























end
end ThreeBoundPositive






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {I V : Type} [Fintype.{0} I] [Fintype.{0} V] (v w : V) (c e : Bool) (a : I) (s : Finset.{0} I),
  Iff
    (@Membership.mem.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (@Finset.instSetLike.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)))
      (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V v c s)
      (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w e) a))
    (And (@Eq.{1} V w v)
      (And (@Eq.{1} Bool e c)
        (@Membership.mem.{0, 0} I (Finset.{0} I)
          (@SetLike.instMembership.{0, 0} (Finset.{0} I) I (@Finset.instSetLike.{0} I)) s a))) := @Sensitivity213981Formal.ThreeBoundPositive.mem_liftBits
