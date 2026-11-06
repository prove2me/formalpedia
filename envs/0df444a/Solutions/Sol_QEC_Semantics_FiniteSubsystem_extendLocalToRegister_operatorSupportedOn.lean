-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.extendLocalToRegister_operatorSupportedOn
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:49:44.009183+00:00
-- url     : https://prove2.me/submissions/c320785c-e619-4b5b-a720-337c03755ab4

-- ID: be2009ff-2bce-409a-93b9-a337e9e0e54b | NAME: QEC.Semantics.FiniteSubsystem.extendLocalToRegister_operatorSupportedOn | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOnRegister (S.extendLocalToRegister A) := by
  exact ⟨A, rfl⟩
