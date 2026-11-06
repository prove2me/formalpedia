-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.restrictLocalFromRegister_extendLocalToRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:16.99789+00:00
-- url     : https://prove2.me/submissions/0bd67cf8-0189-47a1-8304-a568dd97f2a8

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_restrictLocal_extendLocal

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.restrictLocalFromRegister (S.extendLocalToRegister A) = A := by
  unfold restrictLocalFromRegister extendLocalToRegister
  rw [S.registerFactorization.conjOperator_symm_conjOperator]
  exact S.restrictLocal_extendLocal A
end QEC.Semantics.FiniteSubsystem
