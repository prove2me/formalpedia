-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.normalizedSelectedPartialTrace_extendLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:59:09.270439+00:00
-- url     : https://prove2.me/submissions/9c6e7d48-bfea-4d87-b3ee-c9ad243e0801

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_complementFinrank_ne_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_tensor_id


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
    S.normalizedSelectedPartialTrace (S.extendLocal A) = A := by
  change (Module.finrank Complex S.complementSystem : Complex)⁻¹ •
      (partialTraceRightRaw S.selectedSystem S.complementSystem)
        (TensorProduct.map A
          (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)) = A
  rw [partialTraceRightRaw_tensor_id]
  rw [← mul_smul, inv_mul_cancel₀ S.complementFinrank_ne_zero, one_smul]
end QEC.Semantics.FiniteSubsystem
