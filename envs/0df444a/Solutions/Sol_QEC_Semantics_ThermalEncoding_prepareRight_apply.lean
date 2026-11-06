-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.prepareRight_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:01.732206+00:00
-- url     : https://prove2.me/submissions/9f8e1dbd-af32-4094-a50a-3b703600cffa

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_prepareRight_apply_rankOne
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
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
private theorem tensorMap_sum_left {H K : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type} [Fintype ι] (A : ι → Operator H) (B : Operator K) :
    TensorProduct.map (∑ i, A i) B = ∑ i, TensorProduct.map (A i) B := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]
private theorem tensorMap_sum_right {H K : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type} [Fintype ι] (A : Operator H) (B : ι → Operator K) :
    TensorProduct.map A (∑ i, B i) = ∑ i, TensorProduct.map A (B i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, TensorProduct.map_add_right, ih]
end Preparation
namespace PauliLikePair
variable (P : PauliLikePair H)
section Gibbs
variable [Nontrivial P.AuxiliarySpace]
end Gibbs
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
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    prepareRight H K sigma A = TensorProduct.map A sigma.toOperator := by
  let basis := stdOrthonormalBasis Complex H
  rw [QuditSubsystem.operator_eq_sum_rankOne_basis H basis A, map_sum,
    tensorMap_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [prepareRight_apply_rankOne]
  calc
    (∑ j, (InnerProductSpace.rankOne Complex
      (A (basis i) ⊗ₜ[Complex] spectralEnsembleVector sigma j)
      (basis i ⊗ₜ[Complex] spectralEnsembleVector sigma j)).toLinearMap) =
        ∑ j, TensorProduct.map
          (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap
          (InnerProductSpace.rankOne Complex
            (spectralEnsembleVector sigma j)
            (spectralEnsembleVector sigma j)).toLinearMap := by
              apply Finset.sum_congr rfl
              intro j _
              rw [DensityOperator.tensorMap_rankOne]
    _ = TensorProduct.map
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap
        (∑ j, (InnerProductSpace.rankOne Complex
          (spectralEnsembleVector sigma j)
          (spectralEnsembleVector sigma j)).toLinearMap) := by
            rw [tensorMap_sum_right]
    _ = TensorProduct.map
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap
        sigma.toOperator := by
          rw [show (∑ j, (InnerProductSpace.rankOne Complex
            (spectralEnsembleVector sigma j)
            (spectralEnsembleVector sigma j)).toLinearMap) = sigma.toOperator by
              simpa only [spectralEnsembleVector] using sigma.spectralDecomposition.symm]
end QEC.Semantics.ThermalEncoding
