-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.restrictLocalFromRegister_extendLocalToRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:10.746467+00:00
-- url     : https://prove2.me/submissions/07b3da4a-6302-4960-bb1f-c5588fcbc749

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_restrictLocal_extendLocal

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (hq : ∀ i, 0 < q i) (A : Operator S.selectedSystem) :
    S.restrictLocalFromRegister hq (S.extendLocalToRegister A) = A := by
  unfold restrictLocalFromRegister extendLocalToRegister
  rw [S.registerFactorization.conjOperator_symm_conjOperator]
  exact S.restrictLocal_extendLocal hq A
end QEC.Semantics.QuditSubsystem
