-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12TriorthogonalCodeDistillation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:39:11.585232+00:00
-- url     : https://prove2.me/submissions/3c2ba949-a3ac-477a-a2e9-4f12fd623a78

import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Definitions.Def_QEC_Results_Distillation_TriorthogonalDistillation
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockExponent_ne_log_three_div_log_two
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockExponent_succ_tendsto_log_three_div_log_two
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12InputCount_eq_three_mul_output_add_eight
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_cofinalActualOutputError
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_coe_extensionCoefficientLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_pureZLogicalMinimumDistance_two
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_implements_logicalAllSiteT
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BH12EvenFamily.coe_extensionCoefficientLinearEquiv_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily BH12NoisyInjection BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (hq : 0 < q) (hp : 0 < p.rate)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    bh12InputCount q = 3 * bh12OutputCount q + 8 ∧
      Fintype.card (OddRow q) = bh12OutputCount q ∧
        Coding.PureZLogicalMinimumDistance (family q).evenCode (family q).rowCode.dual 2 ∧
          ((family q).encodedCode (isTriorthogonal q)).ImplementsLogicalGate
              (family q).correctedAllSiteT (allSiteT (Index := OddRow q)) ∧
            (InputErrorModel.independent (bh12IndependentInputModel q p)).Permits
                (noisyResources q p) ∧
              (∀ port : OddRow q, ∃ hsuccess : 0 < rawSuccessMass q p,
                0 < (bh12ActualRun q p).successProbability ∧
                  bh12SelectedPortTransportedDensity q p port =
                    OneQubit.diagonalAResource
                      (bh12DecodedMarginalErrorParameter q p hsuccess port) ∧
                  (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
                    quadraticCoefficient q * p.rate ^ 2) ∧
                DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                  (bh12PathScheduleInputSlots q) (bh12PathScheduleOutputSlots q)
                  (bh12PathScheduleTargetError q p)
                  (fun index =>
                    (bh12PathParameter q p index.depth index.path).rate)
                  (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
                  (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) ∧
                  (∀ path : depthOutputPath q 1,
                    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong 1 path =
                      (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost (path 0)) ∧
                    (∀ epsilon : ℝ, 0 < epsilon →
                      ∃ z : Nat, ∀ path : depthOutputPath q z,
                        0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
                          0 < (bh12PathRun q p z path).successProbability ∧
                            (∀ port : OddRow q,
                              bh12PathSelectedPortTransportedDensity q p z path port =
                                OneQubit.diagonalAResource
                                  (bh12TotalNextParameter q
                                    (bh12PathParameter q p z path) port)) ∧
                              (bh12PathParameter q p z path).rate ≤ epsilon) ∧
                      bh12BlockExponent q =
                        Real.log (((3 * bh12OutputCount q + 8 : Nat) : ℝ) /
                          (bh12OutputCount q : ℝ)) / Real.log 2 ∧
                        Tendsto (fun index : Nat => bh12BlockExponent (index + 1)) atTop
                          (𝓝 (Real.log 3 / Real.log 2)) ∧
                          bh12BlockExponent q ≠ Real.log 3 / Real.log 2 ∧
                            (∀ k : Nat, Even k → 0 < k →
                              ∃ index : Nat, 0 < index ∧ k = logicalCount index ∧
                                bh12BlockExponent index =
                                  Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) /
                                    Real.log 2 ∧
                                  Real.log 3 / Real.log 2 < bh12BlockExponent index) := by
  refine ⟨bh12InputCount_eq_three_mul_output_add_eight q, ?_,
    pureZLogicalMinimumDistance_two hq, ?_, bh12IndependentInputModel_permits q p,
    ?_, bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead q p hsmall
      hhalf hstrong hp hq, ?_, ?_, ?_,
    bh12BlockExponent_succ_tendsto_log_three_div_log_two,
    bh12BlockExponent_ne_log_three_div_log_two hq, ?_⟩
  · simpa [bh12OutputCount] using card_oddRow q
  · exact BinaryRowFamily.correctedAllSiteT_implements_logicalAllSiteT
      (family q) (isTriorthogonal q)
  · intro port
    obtain ⟨hsuccess, hactualSuccess, hdensity, hquadratic, _, _, _, _⟩ :=
      bh12OneStepPhysicalInvariant q p port hsmall hhalf (hstrong.trans (by norm_num))
    exact ⟨hsuccess, hactualSuccess, hdensity, hquadratic⟩
  · intro path
    exact bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily q p hsmall
      hhalf hstrong path
  · intro epsilon hepsilon
    exact bh12PathSchedule_cofinalActualOutputError q p hsmall hhalf hstrong epsilon hepsilon
  · exact bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq hq rfl
  · intro k hk hkpos
    exact bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos hk hkpos
end QEC.Distillation.Triorthogonal.BH12Concatenation
