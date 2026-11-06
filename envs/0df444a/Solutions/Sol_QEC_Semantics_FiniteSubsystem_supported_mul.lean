-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.supported_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:45:51.338087+00:00
-- url     : https://prove2.me/submissions/cbd406c8-35c2-4d44-bb6b-baa70238f4fd

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_mul

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι) {A B : Operator (Qubit.QubitRegister ι)}
    (hA : S.OperatorSupportedOnRegister A) (hB : S.OperatorSupportedOnRegister B) :
    S.OperatorSupportedOnRegister (A*B) := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact ⟨a*b, S.extendLocalToRegister_mul a b⟩
end QEC.Semantics.FiniteSubsystem
