-- Prove2me | solution 1 for QEC.Semantics.stableSyndromeLifetimeBridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:26:19.999628+00:00
-- url     : https://prove2.me/submissions/c4192cd9-d0fb-4275-9446-691b3965356b

import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Semantics_Dynamics_StorageHorizon
import Definitions.Def_QEC_Results_QuantumMemory_StableSyndromeStorage
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_commutationPhase_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_anticommute_dressedZ
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_commute_hamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_commute_hamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_dressedX
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_dressedZ
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_hamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_isStarProjection
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_mul_self
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phase_mul_self
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_stabilizerGoodSyndromeProtectedObservable
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_star_phase
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_operator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_mul_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
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
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_protectedObservableStorageHorizon
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.commutationPhase_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_mul_self
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phase_mul_self
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.star_phase
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
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
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics
open QEC.Coding.StabilizerCode
open QEC.Coding.PauliSymplectic
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution
    {iota kappa a : Type}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa] [Fintype a]
    (H : LocalStabilizerHamiltonian (ι := iota) (κ := kappa))
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary iota))
    (jumpError : a → Binary iota)
    (hjumpError : ∀ b, jumpError b ∈ elementaryErrors)
    (beta : ℝ) :
    let logical : ThermalEncoding.PauliLikePair (Qubit.QubitRegister iota) :=
      { x := D.dressedX
        z := D.dressedZ
        x_symmetric :=
          (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedX).mpr
            D.dressedX_adjoint
        z_symmetric :=
          (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedZ).mpr
            D.dressedZ_adjoint
        x_sq := D.dressedX_square
        z_sq := D.dressedZ_square
        anticommute := D.dressedX_anticommute_dressedZ }
    let hhamiltonian : H.operator.IsSymmetric :=
      (LinearMap.isSymmetric_iff_isSelfAdjoint H.operator).mpr
        H.operator_adjoint_eq_self
    let J : a → Operator (Qubit.QubitRegister iota) :=
      fun b ↦ toHermitianQubitOperator (jumpError b)
    let auxiliaryNontrivial : Nontrivial logical.AuxiliarySpace :=
      ThermalEncoding.PauliLikePair.auxiliarySpaceNontrivial logical
    let rhoBeta := @ThermalEncoding.PauliLikePair.physicalGibbsState
      (Qubit.QubitRegister iota) inferInstance inferInstance inferInstance logical
      auxiliaryNontrivial H.operator D.dressedZ_commute_hamiltonian.symm
      hhamiltonian beta
    lindbladDissipator J rhoBeta.toOperator = 0 →
      logical.x.IsSymmetric ∧
      logical.z.IsSymmetric ∧
      logical.x * logical.x = 1 ∧
      logical.z * logical.z = 1 ∧
      logical.x * logical.z = -(logical.z * logical.x) ∧
      Commute logical.x H.operator ∧
      Commute logical.z H.operator ∧
      DecoderDressedLogical.GoodSyndromeProtectedObservable D elementaryErrors ∧
      JumpProtected J D.dressedX (D.goodSyndromeProjector elementaryErrors) ∧
      JumpProtected J D.dressedZ (D.goodSyndromeProjector elementaryErrors) ∧
      ∃ Enc : QuantumChannel Qubit.QubitSpace (Qubit.QubitRegister iota),
        ∃ Dec : QuantumChannel (Qubit.QubitRegister iota) Qubit.QubitSpace,
          (∀ eta : DensityOperator Qubit.QubitSpace,
            Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
          (∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
              (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
            8 * t * lindbladDissipatorNorm J *
                Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) ≤
              delta →
            traceNorm
                (((finiteLindbladEvolutionChannel H.operator J hhamiltonian t
                      ht)
                    |>.mapDensity (Enc.mapDensity eta)).toOperator -
                  (Enc.mapDensity eta).toOperator) ≤ delta ∧
            traceNorm
                ((Dec.mapDensity
                    ((finiteLindbladEvolutionChannel H.operator J hhamiltonian t
                        ht)
                      |>.mapDensity (Enc.mapDensity eta))).toOperator -
                  eta.toOperator) ≤ delta) ∧
          (lindbladDissipatorNorm J *
                Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) = 0 →
            ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
              traceNorm
                  (((finiteLindbladEvolutionChannel H.operator J hhamiltonian t ht)
                      |>.mapDensity (Enc.mapDensity eta)).toOperator -
                    (Enc.mapDensity eta).toOperator) = 0 ∧
              traceNorm
                  ((Dec.mapDensity
                      ((finiteLindbladEvolutionChannel H.operator J hhamiltonian t ht)
                        |>.mapDensity (Enc.mapDensity eta))).toOperator -
                    eta.toOperator) = 0) := by
  dsimp only
  intro hstationary
  let logical : ThermalEncoding.PauliLikePair (Qubit.QubitRegister iota) :=
    { x := D.dressedX
      z := D.dressedZ
      x_symmetric :=
        (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedX).mpr D.dressedX_adjoint
      z_symmetric :=
        (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedZ).mpr D.dressedZ_adjoint
      x_sq := D.dressedX_square
      z_sq := D.dressedZ_square
      anticommute := D.dressedX_anticommute_dressedZ }
  letI : Nontrivial logical.AuxiliarySpace :=
    ThermalEncoding.PauliLikePair.auxiliarySpaceNontrivial logical
  let hhamiltonian : H.operator.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.operator).mpr
      H.operator_adjoint_eq_self
  let J : a → Operator (Qubit.QubitRegister iota) :=
    fun b ↦ toHermitianQubitOperator (jumpError b)
  let P := D.goodSyndromeProjector elementaryErrors
  let rhoBeta := logical.physicalGibbsState H.operator
    D.dressedZ_commute_hamiltonian.symm hhamiltonian beta
  have hprotectedX : JumpProtected J D.dressedX P := by
    intro b
    exact D.elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
      elementaryErrors (hjumpError b)
  have hprotectedZ : JumpProtected J D.dressedZ P := by
    intro b
    exact D.elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
      elementaryErrors (hjumpError b)
  have hmass : clbtGibbsTailMass P rhoBeta =
      Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) := by
    exact congrArg Complex.re
      (D.trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
        elementaryErrors rhoBeta)
  have hhorizon := protectedObservableStorageHorizon logical H.operator
    hhamiltonian beta J P
    (D.goodSyndromeProjector_isStarProjection elementaryErrors)
    (D.goodSyndromeProjector_commute_dressedX elementaryErrors)
    (D.goodSyndromeProjector_commute_dressedZ elementaryErrors)
    D.dressedX_commute_hamiltonian.symm
    D.dressedZ_commute_hamiltonian.symm
    (D.goodSyndromeProjector_commute_hamiltonian elementaryErrors)
    hprotectedX hprotectedZ hstationary
  refine ⟨logical.x_symmetric, logical.z_symmetric, logical.x_sq,
    logical.z_sq, logical.anticommute, D.dressedX_commute_hamiltonian,
    D.dressedZ_commute_hamiltonian,
    D.stabilizerGoodSyndromeProtectedObservable elementaryErrors,
    hprotectedX, hprotectedZ, ?_⟩
  simpa [logical, hhamiltonian, J, P, rhoBeta, hmass] using hhorizon
end QEC.Semantics
