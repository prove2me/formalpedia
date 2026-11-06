-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.tensorSwap_sum_rightTensorCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:42.096197+00:00
-- url     : https://prove2.me/submissions/6fa923a0-7031-4b2f-a2fe-2cf8d77957f3

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_sum_rightTensorCoefficients_tmul
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    tensorSwap H K psi = ∑ j, b j ⊗ₜ[Complex] rightTensorCoefficients b psi j := by
  calc
    tensorSwap H K psi = tensorSwap H K
        (∑ j, rightTensorCoefficients b psi j ⊗ₜ[Complex] b j) :=
      congrArg (tensorSwap H K) (sum_rightTensorCoefficients_tmul b psi).symm
    _ = _ := by simp only [map_sum, tensorSwap_apply_tmul]
end QEC.Semantics.DensityOperator
