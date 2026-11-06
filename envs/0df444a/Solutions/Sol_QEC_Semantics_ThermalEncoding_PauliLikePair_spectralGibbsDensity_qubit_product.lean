-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.spectralGibbsDensity_qubit_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:37.928843+00:00
-- url     : https://prove2.me/submissions/8a28f4e2-0dc8-435e-812e-3e743ceb1b29

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_gibbsProbability_qubit_product
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
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
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)
namespace QEC.Semantics.ThermalEncoding.PauliLikePair
theorem _root_.solution {ι : Type}
    [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι Complex P.AuxiliarySpace)
    (energy : ι → Real) (beta : Real) :
    spectralGibbsDensity
        ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct b)
        (fun qi : Fin 2 × ι => energy qi.2) beta =
      DensityOperator.tensorDensity maximallyMixedQubit
        (spectralGibbsDensity b energy beta) := by
  apply DensityOperator.ext_toOperator
  apply LinearMap.ext
  intro x
  let tb := (EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct b
  conv_lhs => rw [← tb.sum_repr' x]
  conv_rhs => rw [← tb.sum_repr' x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  rintro ⟨q, i⟩ _
  rw [spectralGibbsDensity_apply_basis]
  congr 1
  simp only [tb, OrthonormalBasis.tensorProduct_apply]
  change
    (gibbsProbability beta (fun qi : Fin 2 × ι => energy qi.2) (q, i) :
      Complex) •
        ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i) =
    (DensityOperator.tensorDensity maximallyMixedQubit
      (spectralGibbsDensity b energy beta)).toOperator
      ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i)
  rw [DensityOperator.tensorDensity_toOperator, TensorProduct.map_tmul,
    spectralGibbsDensity_apply_basis]
  change _ =
    (((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
      (EuclideanSpace.basisFun (Fin 2) Complex q)) ⊗ₜ[Complex]
        ((gibbsProbability beta energy i : Complex) • b i)
  rw [LinearMap.smul_apply, Module.End.one_apply]
  have hprob := gibbsProbability_qubit_product beta energy q i
  have hprobC :
      (gibbsProbability beta
        (fun qi : Fin 2 × ι => energy qi.2) (q, i) : Complex) =
        (2 : Complex)⁻¹ * (gibbsProbability beta energy i : Complex) := by
    calc
      (gibbsProbability beta
          (fun qi : Fin 2 × ι => energy qi.2) (q, i) : Complex) =
          ((2 : Real)⁻¹ * gibbsProbability beta energy i : Real) := by
            exact congrArg (fun r : Real => (r : Complex)) hprob
      _ = (2 : Complex)⁻¹ *
          (gibbsProbability beta energy i : Complex) := by norm_num
  rw [hprobC]
  calc
    ((2 : Complex)⁻¹ * (gibbsProbability beta energy i : Complex)) •
          ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i) =
        (2 : Complex)⁻¹ •
          ((gibbsProbability beta energy i : Complex) •
            ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i)) := by
          rw [smul_smul]
    _ = (2 : Complex)⁻¹ •
          ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex]
            ((gibbsProbability beta energy i : Complex) • b i)) := by
          rw [TensorProduct.tmul_smul]
    _ = (((2 : Complex)⁻¹ •
            EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex]
          ((gibbsProbability beta energy i : Complex) • b i)) := by
          rfl
end QEC.Semantics.ThermalEncoding.PauliLikePair
