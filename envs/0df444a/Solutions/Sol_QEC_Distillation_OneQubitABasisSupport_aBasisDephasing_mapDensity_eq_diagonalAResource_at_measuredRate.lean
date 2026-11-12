-- Prove2me | solution 1 for QEC.Distillation.OneQubitABasisSupport.aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:37:12.747204+00:00
-- url     : https://prove2.me/submissions/5c81b8db-3cdd-4ada-84d8-5139c7c2e396

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
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_weight_sum
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aOneDensity_rankOne
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aZeroDensity_rankOne
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
import Theorems.Thm_QEC_Semantics_traceNorm_neg
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
private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem pauliZ_positive_projector_eq_rankOne :
    (1 / 2 : Complex) • (1 + pauliZ) =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex 0)
        (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap := by
  ext psi bit
  fin_cases bit <;>
    simp [LinearMap.smul_apply, LinearMap.add_apply, pauliZ_apply, zPhase,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply]
  all_goals ring
private theorem pauliZ_negative_projector_eq_rankOne :
    (1 / 2 : Complex) • (1 - pauliZ) =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex 1)
        (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap := by
  ext psi bit
  fin_cases bit <;>
    simp [LinearMap.smul_apply, LinearMap.sub_apply, pauliZ_apply, zPhase,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply]
  all_goals ring
private theorem aBasisTransport_conj_positive_projector :
    aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 + pauliZ)) =
      aBasisProjector .positive := by
  unfold aBasisProjector
  rw [show StabilizerOutcome.sign StabilizerOutcome.positive = (1 : Complex) by rfl]
  ext psi
  simp [aBasisObservable, UnitaryTransport.conjOperator, map_add, map_smul]
private theorem aBasisTransport_conj_negative_projector :
    aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 - pauliZ)) =
      aBasisProjector .negative := by
  unfold aBasisProjector
  rw [show StabilizerOutcome.sign StabilizerOutcome.negative = (-1 : Complex) by rfl]
  ext psi
  simp [aBasisObservable, UnitaryTransport.conjOperator, map_sub, map_smul]
  ring
private theorem aBasisProjector_positive_eq_aZeroDensity :
    aBasisProjector .positive = aZeroDensity.toOperator := by
  calc
    aBasisProjector .positive =
        aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 + pauliZ)) :=
      aBasisTransport_conj_positive_projector.symm
    _ = aBasisTransport.conjOperator
        ((InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex 0)
          (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap) := by
      rw [pauliZ_positive_projector_eq_rankOne]
    _ = (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap := by
      rw [QuditSubsystem.conjOperator_rankOne, aBasisTransport_basis_zero]
    _ = aZeroDensity.toOperator := aZeroDensity_rankOne.symm
private theorem aBasisProjector_negative_eq_aOneDensity :
    aBasisProjector .negative = aOneDensity.toOperator := by
  calc
    aBasisProjector .negative =
        aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 - pauliZ)) :=
      aBasisTransport_conj_negative_projector.symm
    _ = aBasisTransport.conjOperator
        ((InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex 1)
          (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap) := by
      rw [pauliZ_negative_projector_eq_rankOne]
    _ = (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
      rw [QuditSubsystem.conjOperator_rankOne, aBasisTransport_basis_one]
    _ = aOneDensity.toOperator := aOneDensity_rankOne.symm
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
  have hcomp : A * (InnerProductSpace.rankOne Complex u u).toLinearMap =
      (InnerProductSpace.rankOne Complex (A u) u).toLinearMap := by
    ext vector
    simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
      InnerProductSpace.rankOne_apply]
  rw [hcomp]
  exact InnerProductSpace.trace_rankOne (A u) u
private theorem inner_apply_real_of_positive
    (rho : DensityOperator QubitSpace) (u : QubitSpace) :
    ((inner Complex u (rho.toOperator u)).re : Complex) =
      inner Complex u (rho.toOperator u) := by
  have hpositive := (LinearMap.isPositive_iff_complex rho.toOperator).mp rho.positive u
  simpa [rho.positive.isSymmetric u u] using hpositive.1
private theorem aBasisDephasing_mapDensity_toOperator_components
    (rho : DensityOperator QubitSpace) :
    (aBasisDephasing.mapDensity rho).toOperator =
      (aBasisInstrument.bornWeight .positive rho : Complex) • aZeroDensity.toOperator +
        (aBasisInstrument.bornWeight .negative rho : Complex) • aOneDensity.toOperator := by
  have hzeroInner : inner Complex aZeroState aZeroState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aZeroState_norm]
    norm_num
  have honeInner : inner Complex aOneState aOneState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aOneState_norm]
    norm_num
  have hplusWeight :
      (aBasisInstrument.bornWeight .positive rho : Complex) =
        inner Complex aZeroState (rho.toOperator aZeroState) := by
    rw [aBasisInstrument_bornWeight_eq_projectorProbability]
    unfold aBasisProjectorProbability
    rw [aBasisProjector_positive_eq_aZeroDensity, aZeroDensity_rankOne,
      trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aZeroState
  have hnegativeWeight :
      (aBasisInstrument.bornWeight .negative rho : Complex) =
        inner Complex aOneState (rho.toOperator aOneState) := by
    rw [aBasisInstrument_bornWeight_eq_projectorProbability]
    unfold aBasisProjectorProbability
    rw [aBasisProjector_negative_eq_aOneDensity, aOneDensity_rankOne,
      trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aOneState
  rw [QuantumChannel.mapDensity_toOperator, aBasisDephasing,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  change (∑ outcome : StabilizerOutcome,
      aBasisProjector outcome *
        (rho.toOperator * LinearMap.adjoint (aBasisProjector outcome))) = _
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {StabilizerOutcome.positive, StabilizerOutcome.negative} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [aBasisProjector_adjoint .positive, aBasisProjector_adjoint .negative,
    aBasisProjector_positive_eq_aZeroDensity, aBasisProjector_negative_eq_aOneDensity,
    aZeroDensity_rankOne, aOneDensity_rankOne,
    rankOne_sandwich aZeroState hzeroInner rho.toOperator,
    rankOne_sandwich aOneState honeInner rho.toOperator,
    ← hplusWeight, ← hnegativeWeight,
    ← aZeroDensity_rankOne, ← aOneDensity_rankOne]
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
    (rho : DensityOperator QubitSpace) (p : ErrorParameter)
    (hrate : p.rate = aBasisInstrument.bornWeight .negative rho) :
    aBasisDephasing.mapDensity rho = diagonalAResource p := by
  have hsum := aBasisInstrument_weight_sum rho
  have hclean : p.cleanWeight = aBasisInstrument.bornWeight .positive rho := by
    unfold ErrorParameter.cleanWeight
    rw [hrate]
    linarith
  apply densityOperator_ext
  rw [aBasisDephasing_mapDensity_toOperator_components,
    diagonalAResource_toOperator, hclean]
  rw [hrate]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
  rfl
end QEC.Distillation.OneQubitABasisSupport
