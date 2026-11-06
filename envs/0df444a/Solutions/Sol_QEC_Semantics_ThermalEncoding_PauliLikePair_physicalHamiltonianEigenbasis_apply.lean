-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.physicalHamiltonianEigenbasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:25:02.318726+00:00
-- url     : https://prove2.me/submissions/c36b9545-b3ef-45f2-b964-d8226ff1de6d

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_factorization_intertwines_auxiliaryOperator
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
variable [Nontrivial P.AuxiliarySpace]
attribute [local instance] QEC.Semantics.ThermalEncoding.PauliLikePair._p2m_local_instance_c824123c1a_1011
omit [Nontrivial P.AuxiliarySpace]
namespace QEC.Semantics.ThermalEncoding.PauliLikePair
theorem _root_.solution
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z)
    (hA : A.IsSymmetric)
    (qi : Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) :
    A (P.physicalHamiltonianEigenbasis A hZ hA qi) =
      (P.physicalHamiltonianEnergies A hZ hA qi : Complex) •
        P.physicalHamiltonianEigenbasis A hZ hA qi := by
  rcases qi with ⟨q, i⟩
  simp only [physicalHamiltonianEigenbasis, OrthonormalBasis.map_apply,
    tensorHamiltonianEigenbasis, OrthonormalBasis.tensorProduct_apply,
    physicalHamiltonianEnergies]
  calc
    A (P.factorization
        (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
          P.auxiliaryHamiltonianEigenbasis A hZ hA i)) =
      P.factorization
        (P.tensorAuxiliaryOperator A hZ
          (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
            P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        exact (P.factorization_intertwines_auxiliaryOperator A hX hZ _).symm
    _ = P.factorization
        (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
          P.auxiliaryOperator A hZ
            (P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        rw [P.tensorAuxiliaryOperator_tmul]
    _ = P.factorization
        (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
          ((P.auxiliaryHamiltonianEnergies A hZ hA i : Complex) •
            P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        rw [auxiliaryHamiltonianEigenbasis, auxiliaryHamiltonianEnergies,
          LinearMap.IsSymmetric.apply_eigenvectorBasis]
        rfl
    _ = P.factorization
        ((P.auxiliaryHamiltonianEnergies A hZ hA i : Complex) •
          (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
            P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        rw [TensorProduct.tmul_smul]
    _ = (P.auxiliaryHamiltonianEnergies A hZ hA i : Complex) •
        P.factorization
          (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
            P.auxiliaryHamiltonianEigenbasis A hZ hA i) := by
        exact map_smul P.factorization.toLinearEquiv _ _
end QEC.Semantics.ThermalEncoding.PauliLikePair
