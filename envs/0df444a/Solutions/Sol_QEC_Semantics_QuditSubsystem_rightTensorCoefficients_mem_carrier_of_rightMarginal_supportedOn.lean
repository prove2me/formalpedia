-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.rightTensorCoefficients_mem_carrier_of_rightMarginal_supportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:59:01.901562+00:00
-- url     : https://prove2.me/submissions/af3c07b4-97eb-486f-a7ed-3c5c46ef728e

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_one_sub_projector_apply_mem_orthogonal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_comp_adjoint_eq_sum_rankOne
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_pureDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_iff_mem
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
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
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (C : QuantumCode H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1)
    (hsupported : DensityOperator.SupportedOn C
      (rightMarginal (pureDensity psi hpsi)))
    (j : Fin (Module.finrank Complex K)) :
    rightTensorCoefficients b psi j ∈ C.carrier := by
  classical
  let a : Fin (Module.finrank Complex K) → H := rightTensorCoefficients b psi
  let rho := rightMarginal (pureDensity psi hpsi)
  have hgram : rho.toOperator = ∑ k,
      (InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap := by
    calc
      rho.toOperator = (rightAmplitude b psi).comp (LinearMap.adjoint (rightAmplitude b psi)) :=
        rightMarginal_pureDensity_toOperator b psi hpsi
      _ = ∑ k, (InnerProductSpace.rankOne Complex
          (rightAmplitude b psi (b k)) (rightAmplitude b psi (b k))).toLinearMap :=
        comp_adjoint_eq_sum_rankOne b (rightAmplitude b psi)
      _ = ∑ k, (InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap := by
        apply Finset.sum_congr rfl
        intro k _
        simp [a, rightAmplitude_apply_basis]
  let v : H := (1 - C.projector : Operator H) (a j)
  have hvorth : v ∈ C.carrierᗮ := by
    simpa [v] using one_sub_projector_apply_mem_orthogonal C (a j)
  have hquad : (∑ k, inner Complex
      ((InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap v) v) = 0 := by
    have hrange : rho.toOperator v ∈ C.carrier := by
      exact hsupported v
    have hinner : inner Complex v (rho.toOperator v) = 0 :=
      (Submodule.mem_orthogonal' C.carrier v).1 hvorth (rho.toOperator v) hrange
    have hinner' : inner Complex (rho.toOperator v) v = 0 := by
      calc
        inner Complex (rho.toOperator v) v = star (inner Complex v (rho.toOperator v)) :=
          (inner_conj_symm (rho.toOperator v) v).symm
        _ = star 0 := congrArg star hinner
        _ = 0 := star_zero Complex
    rw [hgram] at hinner'
    rw [LinearMap.sum_apply, sum_inner] at hinner'
    exact hinner'
  have hterm_pos : ∀ k, LinearMap.IsPositive
      ((InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap : Operator H) := by
    intro k
    exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := Complex) (a k)).toLinearMap
  have hterm_zero : inner Complex
      ((InnerProductSpace.rankOne Complex (a j) (a j)).toLinearMap v) v = 0 := by
    have hfun : (fun k => inner Complex
        ((InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap v) v) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (by
        intro k
        exact (hterm_pos k).inner_nonneg_left v)).mp hquad
    exact congrFun hfun j
  have hajv : inner Complex (a j) v = 0 := by
    have hproduct : inner Complex (a j) v * inner Complex v (a j) = 0 := by
      simpa [InnerProductSpace.rankOne_apply] using hterm_zero
    rcases mul_eq_zero.mp hproduct with hzero | hzero
    · exact hzero
    · exact inner_eq_zero_symm.mp hzero
  have hprojected_mem : C.projector (a j) ∈ C.carrier :=
    C.projector_mem_carrier (a j)
  have hprojected_orthogonal : inner Complex (C.projector (a j)) v = 0 := by
    have hright : inner Complex v (C.projector (a j)) = 0 :=
      (Submodule.mem_orthogonal' C.carrier v).1 hvorth
        (C.projector (a j)) hprojected_mem
    calc
      inner Complex (C.projector (a j)) v =
          star (inner Complex v (C.projector (a j))) :=
            (inner_conj_symm (C.projector (a j)) v).symm
      _ = star 0 := congrArg star hright
      _ = 0 := star_zero Complex
  have hsplit : a j = C.projector (a j) + v := by
    change a j = C.projector (a j) + (a j - C.projector (a j))
    module
  have hvself : inner Complex v v = 0 := by
    have hdecompose : inner Complex (a j) v =
        inner Complex (C.projector (a j)) v + inner Complex v v := by
      calc
        inner Complex (a j) v = inner Complex (C.projector (a j) + v) v := by
          rw [← hsplit]
        _ = inner Complex (C.projector (a j)) v + inner Complex v v :=
          inner_add_left _ _ _
    rw [hajv, hprojected_orthogonal] at hdecompose
    simpa using hdecompose.symm
  have hvzero : v = 0 := by
    by_contra hne
    exact (inner_self_ne_zero.mpr hne) hvself
  apply (C.projector_eq_self_iff_mem).1
  change C.projector (a j) = a j
  change a j - C.projector (a j) = 0 at hvzero
  exact (sub_eq_zero.mp hvzero).symm
end QEC.Semantics.QuditSubsystem
