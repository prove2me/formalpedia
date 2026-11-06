-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.tensorDensityLeft_operatorNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:33.436847+00:00
-- url     : https://prove2.me/submissions/1c682c28-d956-4c9c-80b9-ce9418363d5f

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_DensityOperator_one_sub_toOperator_positive
import Theorems.Thm_QEC_Semantics_ThermalEncoding_tensorMap_positive
import Theorems.Thm_QEC_Semantics_ThermalEncoding_operatorNorm_le_one_of_positive_one_sub
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) :
    ‖LinearMap.toContinuousLinearMap
      (TensorProduct.map rho.toOperator (1 : Operator K))‖ ≤ 1 := by
  apply operatorNorm_le_one_of_positive_one_sub
  · exact tensorMap_positive rho.toOperator 1 rho.positive
      LinearMap.isPositive_one
  · have hpos := tensorMap_positive (1 - rho.toOperator) (1 : Operator K)
        (QEC.Semantics.ThermalEncoding.DensityOperator.one_sub_toOperator_positive rho)
        LinearMap.isPositive_one
    have heq :
        (1 : Operator (CompositeSystem H K)) -
            TensorProduct.map rho.toOperator (1 : Operator K) =
          TensorProduct.map (1 - rho.toOperator) (1 : Operator K) := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          simpa [TensorProduct.map_tmul] using
            (TensorProduct.sub_tmul x (rho.toOperator x) y).symm
      | add x y hx hy => simp [map_add, hx, hy]
    rw [heq]
    exact hpos
end QEC.Semantics.ThermalEncoding
