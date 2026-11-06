-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_eq_encodedObservable_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:56.264583+00:00
-- url     : https://prove2.me/submissions/6af25cae-235a-4664-85b1-f0d61e655679

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalEncoding_apply
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalReferenceState_toOperator
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


section
noncomputable section
namespace QEC
namespace Semantics
namespace ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace DensityOperator
end DensityOperator
namespace PauliLikePair
variable (P : PauliLikePair H)
end PauliLikePair
section Preparation
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
end Preparation
namespace PauliLikePair
variable (P : PauliLikePair H)
section Gibbs
variable [Nontrivial P.AuxiliarySpace]
end Gibbs
private theorem encoded_tensor_mul_reference
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    TensorProduct.map ((2 : Complex) • eta.toOperator)
        (1 : Operator P.AuxiliarySpace) *
      TensorProduct.map ((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
        sigma.toOperator =
      TensorProduct.map eta.toOperator sigma.toOperator := by
  rw [← TensorProduct.map_mul]
  congr 1
  · apply LinearMap.ext
    intro q
    simp
end PauliLikePair
end ThermalEncoding
end Semantics
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)
namespace QEC.Semantics.ThermalEncoding.PauliLikePair
theorem _root_.solution
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalEncoding sigma eta.toOperator =
      P.encodedObservable eta * (P.thermalReferenceState sigma).toOperator := by
  rw [P.thermalEncoding_apply, encodedObservable,
    P.thermalReferenceState_toOperator, ← P.factorization.conjOperator_mul,
    encoded_tensor_mul_reference]
end QEC.Semantics.ThermalEncoding.PauliLikePair
