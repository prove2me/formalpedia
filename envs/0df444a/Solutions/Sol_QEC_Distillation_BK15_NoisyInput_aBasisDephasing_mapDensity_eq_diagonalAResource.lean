-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.aBasisDephasing_mapDensity_eq_diagonalAResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:18:32.950398+00:00
-- url     : https://prove2.me/submissions/561fcd38-63c2-4f27-8f27-15379ad5727e

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aZeroDensity_eq_phaseStateDensity
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisProjector_positive_eq_aZeroDensity_toOperator
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisProjector_negative_eq_aOneDensity_toOperator
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_OneQubitMagic_trace_mul_rankOne
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
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


section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem aZeroDensity_toOperator_rankOne :
    aZeroDensity.toOperator =
      (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap := by
  rw [aZeroDensity_eq_phaseStateDensity, phaseStateDensity_toOperator]
  rfl
private theorem aOneDensity_toOperator_rankOne :
    aOneDensity.toOperator =
      (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
  rw [aOneDensity, UnitaryTransport.conjDensity_toOperator,
    aZeroDensity_toOperator_rankOne, QuditSubsystem.conjOperator_rankOne]
  rfl
namespace BK15Epsilon
end BK15Epsilon
private theorem rankOne_sandwich
    (u : QubitSpace) (_hu : inner Complex u u = 1) (A : Operator QubitSpace) :
    (InnerProductSpace.rankOne Complex u u).toLinearMap *
        (A * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
        (inner Complex u (A u)) •
        (InnerProductSpace.rankOne Complex u u).toLinearMap := by
  ext vector
  simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply]
  ring
private theorem trace_rankOne_mul
    (u : QubitSpace) (A : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
      ((InnerProductSpace.rankOne Complex u u).toLinearMap * A) =
        inner Complex u (A u) := by
  rw [LinearMap.trace_mul_comm]
  exact trace_mul_rankOne A u
private theorem inner_apply_real_of_positive
    (rho : DensityOperator QubitSpace) (u : QubitSpace) :
    ((inner Complex u (rho.toOperator u)).re : Complex) =
      inner Complex u (rho.toOperator u) := by
  have hpositive := (LinearMap.isPositive_iff_complex rho.toOperator).mp rho.positive u
  simpa [rho.positive.isSymmetric u u] using hpositive.1
private theorem aBasisSquaredOverlap_add_negative
    (rho : DensityOperator QubitSpace) :
    aInputSquaredOverlap rho +
        projectionSquaredOverlap (aBasisProjector .negative) rho = 1 := by
  unfold aInputSquaredOverlap projectionSquaredOverlap
  have htrace :
      LinearMap.trace Complex QubitSpace
          (aBasisProjector .positive * rho.toOperator) +
        LinearMap.trace Complex QubitSpace
          (aBasisProjector .negative * rho.toOperator) = 1 := by
    calc
      LinearMap.trace Complex QubitSpace
          (aBasisProjector .positive * rho.toOperator) +
        LinearMap.trace Complex QubitSpace
          (aBasisProjector .negative * rho.toOperator) =
          LinearMap.trace Complex QubitSpace
            ((aBasisProjector .positive + aBasisProjector .negative) * rho.toOperator) := by
              rw [add_mul, map_add]
      _ = LinearMap.trace Complex QubitSpace rho.toOperator := by
        rw [aBasisProjector_add, one_mul]
      _ = 1 := rho.trace_one
  have hre := congrArg Complex.re htrace
  exact_mod_cast hre
private theorem aBasisDephasing_mapDensity_toOperator_eq_components
    (rho : DensityOperator QubitSpace) :
    (aBasisDephasing.mapDensity rho).toOperator =
      (aInputSquaredOverlap rho : Complex) • aZeroDensity.toOperator +
        (aInputError rho : Complex) • aOneDensity.toOperator := by
  have hzeroInner : inner Complex aZeroState aZeroState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aZeroState_norm]
    norm_num
  have honeInner : inner Complex aOneState aOneState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aOneState_norm]
    norm_num
  have hplusWeight :
      (aInputSquaredOverlap rho : Complex) =
        inner Complex aZeroState (rho.toOperator aZeroState) := by
    unfold aInputSquaredOverlap projectionSquaredOverlap
    rw [aBasisProjector_positive_eq_aZeroDensity_toOperator,
      aZeroDensity_toOperator_rankOne, trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aZeroState
  have hnegativeSquaredWeight :
      (projectionSquaredOverlap (aBasisProjector .negative) rho : Complex) =
        inner Complex aOneState (rho.toOperator aOneState) := by
    unfold projectionSquaredOverlap
    rw [aBasisProjector_negative_eq_aOneDensity_toOperator,
      aOneDensity_toOperator_rankOne, trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aOneState
  have hnegativeWeight :
      (aInputError rho : Complex) =
        inner Complex aOneState (rho.toOperator aOneState) := by
    have hsum := aBasisSquaredOverlap_add_negative rho
    unfold aInputError
    have hreal : projectionSquaredOverlap (aBasisProjector .negative) rho =
        1 - aInputSquaredOverlap rho := by
      linarith
    rw [← hreal, hnegativeSquaredWeight]
  rw [QuantumChannel.mapDensity_toOperator, aBasisDephasing,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  change (∑ outcome : Coding.PauliSymplectic.StabilizerOutcome,
      aBasisProjector outcome *
        (rho.toOperator * LinearMap.adjoint (aBasisProjector outcome))) = _
  rw [show (Finset.univ : Finset Coding.PauliSymplectic.StabilizerOutcome) =
      {Coding.PauliSymplectic.StabilizerOutcome.positive,
        Coding.PauliSymplectic.StabilizerOutcome.negative} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [aBasisProjector_adjoint .positive, aBasisProjector_adjoint .negative,
    aBasisProjector_positive_eq_aZeroDensity_toOperator,
    aBasisProjector_negative_eq_aOneDensity_toOperator,
    aZeroDensity_toOperator_rankOne, aOneDensity_toOperator_rankOne,
    rankOne_sandwich aZeroState hzeroInner rho.toOperator,
    rankOne_sandwich aOneState honeInner rho.toOperator,
    ← hplusWeight, ← hnegativeWeight,
    ← aZeroDensity_toOperator_rankOne, ← aOneDensity_toOperator_rankOne]
section
set_option maxRecDepth 65536
end
end NoisyInput
end BK15
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.BK15.NoisyInput
theorem _root_.solution
    (rho : DensityOperator QubitSpace) (epsilon : BK15Epsilon)
    (hepsilon : epsilon.epsilon = aInputError rho) :
    aBasisDephasing.mapDensity rho = diagonalAResource epsilon := by
  have hclean : epsilon.cleanWeight = aInputSquaredOverlap rho := by
    unfold BK15Epsilon.cleanWeight
    rw [hepsilon]
    unfold aInputError
    ring
  apply densityOperator_ext
  rw [aBasisDephasing_mapDensity_toOperator_eq_components]
  rw [diagonalAResource, DensityOperator.convexCombination_toOperator]
  change (aInputSquaredOverlap rho : Complex) • aZeroDensity.toOperator +
      (aInputError rho : Complex) • aOneDensity.toOperator =
    ∑ bit ∈ (Finset.univ : Finset (Fin 2)),
      (aInputWeight epsilon bit : Complex) • (aInputComponent bit).toOperator
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp [aInputWeight, aInputComponent, hclean, hepsilon]
end QEC.Distillation.BK15.NoisyInput
