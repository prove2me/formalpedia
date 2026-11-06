-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_tensorDensity_eq_double_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:00.983337+00:00
-- url     : https://prove2.me/submissions/44cc9756-a748-40ba-aeb3-4b66a008418b

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_apply_spectralTensorBasis
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


attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator

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
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).vonNeumannEntropy = ∑ i, ∑ j,
      entropyTerm (rho.spectralEigenvalues i * sigma.spectralEigenvalues j) := by
  let b := rho.spectralEigenbasis.tensorProduct sigma.spectralEigenbasis
  have hdiagonal := vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis
    (tensorDensity rho sigma) b
    (fun ij => rho.spectralEigenvalues ij.1 * sigma.spectralEigenvalues ij.2) (by
      intro ij
      dsimp [b]
      rcases ij with ⟨i, j⟩
      rw [OrthonormalBasis.tensorProduct_apply]
      exact tensorDensity_apply_spectralTensorBasis rho sigma i j)
  rw [hdiagonal, Fintype.sum_prod_type]
end QEC.Semantics.DensityOperator
