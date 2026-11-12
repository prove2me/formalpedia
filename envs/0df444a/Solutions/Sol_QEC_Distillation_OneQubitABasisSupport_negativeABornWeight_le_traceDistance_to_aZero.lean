-- Prove2me | solution 1 for QEC.Distillation.OneQubitABasisSupport.negativeABornWeight_le_traceDistance_to_aZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:36:57.818064+00:00
-- url     : https://prove2.me/submissions/c98b92a3-ba94-40af-92b6-426e9f1de7ca

import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_branch_aZero
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_norm_trace_le_traceNorm
import Theorems.Thm_QEC_Semantics_operatorNorm_projection_le
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
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
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
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
attribute [local simp] QEC.Semantics.traceNorm_neg


section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitABasisSupport
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
private theorem aBasisInstrument_bornWeight_eq_projectorProbability
    (outcome : StabilizerOutcome) (rho : DensityOperator QubitSpace) :
    aBasisInstrument.bornWeight outcome rho =
      aBasisProjectorProbability outcome rho := by
  classical
  unfold FiniteInstrument.bornWeight aBasisProjectorProbability
  rw [FiniteInstrument.branchOperator_apply]
  rw [Fintype.sum_eq_single outcome]
  · simp only [aBasisInstrument, aBasisDephasingKrausFamily, id_eq, ↓reduceIte]
    change Complex.re (LinearMap.trace Complex QubitSpace
      (aBasisProjector outcome *
        (rho.toOperator * LinearMap.adjoint (aBasisProjector outcome)))) = _
    rw [aBasisProjector_adjoint]
    calc
      Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome *
            (rho.toOperator * aBasisProjector outcome))) =
          Complex.re (LinearMap.trace Complex QubitSpace
            ((aBasisProjector outcome * rho.toOperator) *
              aBasisProjector outcome)) := by
            congr 2
      _ = Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome *
            (aBasisProjector outcome * rho.toOperator))) := by
            rw [LinearMap.trace_mul_comm]
      _ = Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome * rho.toOperator)) := by
            rw [← mul_assoc, aBasisProjector_idempotent]
  · intro other hother
    simp [aBasisInstrument, aBasisDephasingKrausFamily, hother]
private theorem negative_aBasisProjector_isStarProjection :
    IsStarProjection (aBasisProjector .negative) := by
  rw [LinearMap.isStarProjection_iff_isSymmetricProjection]
  constructor
  · exact aBasisProjector_idempotent .negative
  · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    exact aBasisProjector_adjoint .negative
private theorem negative_aBasisProjector_aZero_trace_zero :
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative * aZeroDensity.toOperator)).re = 0 := by
  change aBasisProjectorProbability .negative aZeroDensity = 0
  rw [← aBasisInstrument_bornWeight_eq_projectorProbability]
  rw [FiniteInstrument.bornWeight, aBasisInstrument_branch_aZero]
  have hne : (StabilizerOutcome.negative : StabilizerOutcome) ≠ .positive := by decide
  rw [if_neg hne]
  norm_num
end OneQubitABasisSupport
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitABasisSupport
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
namespace QEC.Distillation.OneQubitABasisSupport
theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    aBasisInstrument.bornWeight .negative rho ≤
      traceNorm (rho.toOperator - aZeroDensity.toOperator) := by
  let P : Operator QubitSpace := aBasisProjector .negative
  have hprojector : IsStarProjection P := negative_aBasisProjector_isStarProjection
  have hideal :
      (LinearMap.trace Complex QubitSpace (P * aZeroDensity.toOperator)).re = 0 :=
    negative_aBasisProjector_aZero_trace_zero
  have hraw :
      aBasisInstrument.bornWeight .negative rho =
        (LinearMap.trace Complex QubitSpace (P * rho.toOperator)).re :=
    aBasisInstrument_bornWeight_eq_projectorProbability .negative rho
  have hcenter :
      (LinearMap.trace Complex QubitSpace (P * rho.toOperator)).re =
        (LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))).re := by
    rw [mul_sub, map_sub, Complex.sub_re, hideal, sub_zero]
  calc
    aBasisInstrument.bornWeight .negative rho =
        (LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))).re := hraw.trans hcenter
    _ ≤ |(LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))).re| := le_abs_self _
    _ ≤ ‖LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ traceNorm (P * (rho.toOperator - aZeroDensity.toOperator)) :=
      norm_trace_le_traceNorm _
    _ ≤ operatorNorm P * traceNorm (rho.toOperator - aZeroDensity.toOperator) :=
      traceNorm_mul_left_le _ _
    _ ≤ 1 * traceNorm (rho.toOperator - aZeroDensity.toOperator) := by
      exact mul_le_mul_of_nonneg_right
        (operatorNorm_projection_le P hprojector) (traceNorm_nonneg _)
    _ = traceNorm (rho.toOperator - aZeroDensity.toOperator) := by ring
end QEC.Distillation.OneQubitABasisSupport
