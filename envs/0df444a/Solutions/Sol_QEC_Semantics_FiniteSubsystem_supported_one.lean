-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.supported_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:48:31.763817+00:00
-- url     : https://prove2.me/submissions/a91c2ce2-d832-4e45-9b60-da9894e0de05

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (S : FiniteSubsystem ι) : S.OperatorSupportedOnRegister 1 := by
  refine ⟨1, ?_⟩
  rw [FiniteSubsystem.extendLocalToRegister]
  have h : S.extendLocal 1 = 1 := by
    apply TensorProduct.ext'
    intro x y
    simp [FiniteSubsystem.extendLocal]
  rw [h, UnitaryTransport.conjOperator_one]
