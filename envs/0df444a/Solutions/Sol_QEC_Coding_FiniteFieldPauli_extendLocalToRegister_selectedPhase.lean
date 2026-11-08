-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.extendLocalToRegister_selectedPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:40.804203+00:00
-- url     : https://prove2.me/submissions/1173320e-45a3-4467-81ff-5fbb1bfea8f8

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Coding_QLDPC_BPTMeasurementDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_phase_basis
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_registerUnitary_symm_apply_basis
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_wordPairing_restrictWordToRegion_eq
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_selectedPhase_apply_basis
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
import Theorems.Thm_QEC_Semantics_FiniteAlphabet_registerUnitary_apply_basis
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_symm_apply_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
set_option maxRecDepth 4096
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    {ι' : Type u} [Fintype ι']
    (S : @Semantics.QuditSubsystem ι' inferInstance (Classical.decEq ι')
      (fun _ : ι' => Fintype.card F))
    (z : Word F ι') (hz : ∀ j, j ∉ S.selected → z j = 0) :
    S.extendLocalToRegister (selectedPhase S z) =
      (registerUnitary (F := F) (ι' := ι')).conjOperator (phase z) := by
  let _ : DecidableEq ι' := Classical.decEq ι'
  apply (EuclideanSpace.basisFun
    (Semantics.Qudit.Label (fun _ : ι' => Fintype.card F)) Complex).toBasis.ext
  intro labels
  let a : Word F ι' := (fieldLabelEquiv (F := F)).symm labels
  have hlabels : labels = fieldLabelEquiv (F := F) a :=
    ((fieldLabelEquiv (F := F)).apply_symm_apply labels).symm
  rw [hlabels]
  change S.extendLocalToRegister (selectedPhase S z)
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
    (registerUnitary (F := F) (ι' := ι')).conjOperator (phase z)
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a))
  unfold Semantics.QuditSubsystem.extendLocalToRegister
  rw [Semantics.UnitaryTransport.conjOperator_apply]
  simp only [Semantics.UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.symm_symm]
  rw [S.registerFactorization_apply_basis,
    splitLabel_fieldLabelEquiv_first,
    splitLabel_fieldLabelEquiv_second,
    S.extendLocal_apply_tmul,
    selectedPhase_apply_basis,
    ← TensorProduct.smul_tmul', map_smul]
  have hfactor := S.registerFactorization_symm_apply_basis
    (fieldLabelEquiv (F := F) (restrictWordToRegion S a),
      fieldLabelEquiv (F := F) (restrictWordToComplement S a))
  change _ • S.registerFactorization.symm.toLinearEquiv
      ((EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) (restrictWordToRegion S a))) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) (restrictWordToComplement S a)))) = _
  rw [hfactor]
  have hRecombine : S.recombineLabel
      (fieldLabelEquiv (F := F) (restrictWordToRegion S a),
        fieldLabelEquiv (F := F) (restrictWordToComplement S a)) =
      fieldLabelEquiv (F := F) a := by
    funext j
    by_cases hj : j ∈ S.selected
    · simp [Semantics.QuditSubsystem.recombineLabel, hj,
        restrictWordToRegion, fieldLabelEquiv]
    · simp [Semantics.QuditSubsystem.recombineLabel, hj,
        restrictWordToComplement, fieldLabelEquiv]
  rw [hRecombine, Semantics.UnitaryTransport.conjOperator_apply]
  have hinv : (registerUnitary (F := F) (ι' := ι')).toLinearEquiv.symm
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex a := by
    change (registerUnitary (F := F) (ι' := ι')).symm
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) = _
    exact registerUnitary_symm_apply_basis (F := F) a
  rw [hinv, phase_basis, map_smul]
  rw [wordPairing_restrictWordToRegion_eq S z a hz]
  congr 1
  exact (Semantics.FiniteAlphabet.registerUnitary_apply_basis F ι' a).symm
end QEC.Coding.FiniteFieldPauli
