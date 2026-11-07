-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.semanticStabilizerDistance_of_algebraicCSSMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:41:03.517206+00:00
-- url     : https://prove2.me/submissions/f30c2712-dfc9-46ff-bb31-b44b71b0952e

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_xPart_le_weight
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_zPart_le_weight
import Theorems.Thm_QEC_Coding_PauliSymplectic_inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_StabilizerCode_semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {iota kappaP kappaQ : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappaP] [Fintype kappaQ]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p)
        (parityCheckRow Q q) = 0)
    {distance : Nat}
    (hDistance : AlgebraicCSSMinimumDistance
      (parityCheckRowCode Q)
      (parityCheckRowCode P) distance) :
    StabilizerCode.SemanticStabilizerDistance
      (PauliSymplectic.binaryCSSSourceValidStabilizerOfParityChecks
        P Q horth) distance := by
  rw [StabilizerCode.semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff]
  rcases hDistance with ⟨word, hword, hweight, hleast⟩
  rcases hword with hX | hZ
  · refine ⟨PauliSymplectic.cssXCheck word, ?_, ?_, ?_, ?_⟩
    have hXKernel := hX.1
    rw [parityCheckRowCode_dual_eq_kernelCode] at hXKernel
    · exact
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssXCheck word)).2
          ⟨by simpa using hXKernel,
            (parityCheckKernelCode Q).carrier.zero_mem⟩
    · intro hgenerated
      have hcomponents :=
        (PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssXCheck word)).1 hgenerated
      exact hX.2 hcomponents.1
    · simpa using
        (PauliSymplectic.weight_cssXCheck_eq_hammingWeight word).trans hweight
    · intro error hnormalizer houtside
      have hnormalizerComponents :=
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth error).1 hnormalizer
      have houtsideComponents :
          error.vector.xPart ∉
              (parityCheckRowCode Q).carrier ∨
            error.vector.zPart ∉
              (parityCheckRowCode P).carrier := by
        by_contra hnot
        push_neg at hnot
        exact houtside
          ((PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth error).2 hnot)
      rcases houtsideComponents with hxOutside | hzOutside
      · have hxDual := hnormalizerComponents.1
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hxDual
        exact (hleast error.vector.xPart (Or.inl
          ⟨hxDual, hxOutside⟩)).trans
          (PauliSymplectic.hammingWeight_xPart_le_weight error)
      · have hzDual := hnormalizerComponents.2
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hzDual
        exact (hleast error.vector.zPart (Or.inr
          ⟨hzDual, hzOutside⟩)).trans
          (PauliSymplectic.hammingWeight_zPart_le_weight error)
  · refine ⟨PauliSymplectic.cssZCheck word, ?_, ?_, ?_, ?_⟩
    have hZKernel := hZ.1
    rw [parityCheckRowCode_dual_eq_kernelCode] at hZKernel
    · exact
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssZCheck word)).2
          ⟨(parityCheckKernelCode P).carrier.zero_mem,
            by simpa using hZKernel⟩
    · intro hgenerated
      have hcomponents :=
        (PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (PauliSymplectic.cssZCheck word)).1 hgenerated
      exact hZ.2 hcomponents.2
    · simpa using
        (PauliSymplectic.weight_cssZCheck_eq_hammingWeight word).trans hweight
    · intro error hnormalizer houtside
      have hnormalizerComponents :=
        (PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth error).1 hnormalizer
      have houtsideComponents :
          error.vector.xPart ∉
              (parityCheckRowCode Q).carrier ∨
            error.vector.zPart ∉
              (parityCheckRowCode P).carrier := by
        by_contra hnot
        push_neg at hnot
        exact houtside
          ((PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth error).2 hnot)
      rcases houtsideComponents with hxOutside | hzOutside
      · have hxDual := hnormalizerComponents.1
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hxDual
        exact (hleast error.vector.xPart (Or.inl
          ⟨hxDual, hxOutside⟩)).trans
          (PauliSymplectic.hammingWeight_xPart_le_weight error)
      · have hzDual := hnormalizerComponents.2
        rw [← parityCheckRowCode_dual_eq_kernelCode] at hzDual
        exact (hleast error.vector.zPart (Or.inr
          ⟨hzDual, hzOutside⟩)).trans
          (PauliSymplectic.hammingWeight_zPart_le_weight error)
end QEC.Coding.QuantumTanner
