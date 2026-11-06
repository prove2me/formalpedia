-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.supported_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:45:29.581009+00:00
-- url     : https://prove2.me/submissions/2f991817-3dba-4fbd-9e9c-d6b69e99a038

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_smul_scalar

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι) (c : ℂ)
    {A : Operator (Qubit.QubitRegister ι)} (hA : S.OperatorSupportedOnRegister A) :
    S.OperatorSupportedOnRegister (c • A) := by
  obtain ⟨a,rfl⟩ := hA
  exact ⟨c • a, S.extendLocalToRegister_smul_scalar c a⟩
end QEC.Semantics.FiniteSubsystem
