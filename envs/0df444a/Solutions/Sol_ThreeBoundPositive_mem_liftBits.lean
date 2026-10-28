-- Prove2me | solution 1 for ThreeBoundPositive.mem_liftBits
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:39:56.148282+00:00
-- url     : https://prove2.me/submissions/95d00f5a-3123-4ac5-97d4-5e40ee1ac286

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
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
namespace ThreeBoundPositive
end ThreeBoundPositive
open ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

@[simp] theorem solution (v w : V) (c e : Bool) (a : I) (s : Finset I) :
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
