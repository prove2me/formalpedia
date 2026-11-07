-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finrank_ker_jointTensorMap_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:55.522841+00:00
-- url     : https://prove2.me/submissions/c1946038-14e6-489a-a0bb-e5979208d583

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type u} {M M' N N' : Type v}
    [Field F]
    [AddCommGroup M] [Module F M] [Module.Free F M] [Module.Finite F M]
    [AddCommGroup M'] [Module F M'] [Module.Free F M'] [Module.Finite F M']
    [AddCommGroup N] [Module F N] [Module.Free F N] [Module.Finite F N]
    [AddCommGroup N'] [Module F N'] [Module.Free F N'] [Module.Finite F N']
    (f : M →ₗ[F] M') (g : N →ₗ[F] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Module.finrank F (LinearMap.ker (jointTensorMap f g)) =
      Module.finrank F (LinearMap.ker f) *
        Module.finrank F (LinearMap.ker g) := by
  let A : Submodule F (M ⊗[F] N) := LinearMap.ker (f.rTensor N)
  let B : Submodule F (M ⊗[F] N) := LinearMap.ker (g.lTensor M)
  have hA : A = LinearMap.range ((LinearMap.ker f).subtype.rTensor N) := by
    change LinearMap.ker (f.rTensor N) = _
    exact (Module.Flat.rTensor_exact N f.exact_subtype_ker_map).linearMap_ker_eq
  have hB : B = LinearMap.range ((LinearMap.ker g).subtype.lTensor M) := by
    change LinearMap.ker (g.lTensor M) = _
    exact (Module.Flat.lTensor_exact M g.exact_subtype_ker_map).linearMap_ker_eq
  have hAInjective :
      Function.Injective ((LinearMap.ker f).subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap
      (LinearMap.ker f).subtype (LinearMap.ker f).injective_subtype
  have hBInjective :
      Function.Injective ((LinearMap.ker g).subtype.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (LinearMap.ker g).subtype (LinearMap.ker g).injective_subtype
  have hAfinrank :
      Module.finrank F A =
        Module.finrank F (LinearMap.ker f) * Module.finrank F N := by
    rw [hA, LinearMap.finrank_range_of_inj hAInjective]
    exact Module.finrank_tensorProduct
  have hBfinrank :
      Module.finrank F B =
        Module.finrank F M * Module.finrank F (LinearMap.ker g) := by
    rw [hB, LinearMap.finrank_range_of_inj hBInjective]
    exact Module.finrank_tensorProduct
  have hMapKer := TensorProduct.map_ker
    (hfg := f.exact_subtype_ker_map) (hg := hf)
    (hfg' := g.exact_subtype_ker_map) (hg' := hg)
  have hSup : A ⊔ B = LinearMap.ker (TensorProduct.map f g) := by
    rw [hA, hB, sup_comm]
    exact hMapKer.symm
  have hF := f.finrank_range_add_finrank_ker
  have hG := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hF
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at hG
  have hMap := (TensorProduct.map f g).finrank_range_add_finrank_ker
  have hMapSurjective : Function.Surjective (TensorProduct.map f g) :=
    TensorProduct.map_surjective hf hg
  rw [LinearMap.range_eq_top.mpr hMapSurjective, finrank_top,
    Module.finrank_tensorProduct, Module.finrank_tensorProduct] at hMap
  have hGrass := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hSup, hAfinrank, hBfinrank] at hGrass
  have hJointKer : LinearMap.ker (jointTensorMap f g) = A ⊓ B := by
    simp [jointTensorMap, A, B, LinearMap.ker_prod]
  rw [hJointKer]
  nlinarith
end QEC.Coding.HypergraphProduct
