-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.leftMarginal_pureDensity_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:22.841979+00:00
-- url     : https://prove2.me/submissions/d18af039-6904-4a82-8233-b66b2b59afb5

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_pureDensity_toOperator_sum
import Theorems.Thm_QEC_Semantics_DensityOperator_inner_eq_sum_reprs
import Theorems.Thm_QEC_Semantics_DensityOperator_inner_rankOne_basis_apply
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
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    LinearMap.toMatrix bK.toBasis bK.toBasis
      (leftMarginal (pureDensity psi hpsi)).toOperator =
      ((coefficientMatrix bH bK psi).conjTranspose * coefficientMatrix bH bK psi).transpose := by
  ext r s
  rw [LinearMap.toMatrix_apply]
  change bK.repr ((leftMarginal (pureDensity psi hpsi)).toOperator (bK s)) r = _
  rw [leftMarginal_pureDensity_toOperator_sum bK psi hpsi]
  rw [OrthonormalBasis.repr_apply_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum]
  simp_rw [inner_smul_right]
  simp_rw [inner_rankOne_basis_apply bK]
  simp [eq_comm]
  rw [inner_eq_sum_reprs bH]
  simp [coefficientMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    LinearMap.toMatrix_apply]
end QEC.Semantics.DensityOperator
