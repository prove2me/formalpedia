-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.leftMarginal_pureDensity_toOperator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:17.101578+00:00
-- url     : https://prove2.me/submissions/43ab8886-80b8-4ef5-a07d-4a8f0931b659

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_rankOne_sum_sum
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorSwap_sum_rightTensorCoefficients
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
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
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (leftMarginal (pureDensity psi hpsi)).toOperator =
      ∑ i, ∑ j,
        (inner Complex (rightTensorCoefficients b psi j) (rightTensorCoefficients b psi i)) •
          (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap := by
  change partialTraceRightRaw K H
    ((tensorSwap H K).conjOperator
      ((InnerProductSpace.rankOne Complex psi psi).toLinearMap)) = _
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [tensorSwap_sum_rightTensorCoefficients b psi]
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
end QEC.Semantics.DensityOperator
