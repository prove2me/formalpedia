-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:12:15.346851+00:00
-- url     : https://prove2.me/submissions/0a97f987-5357-4979-92ab-a160ec308a59

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
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
namespace BK15Epsilon
end BK15Epsilon
section
set_option maxRecDepth 65536
end
private theorem conjDensity_convexCombination
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type v} [Fintype ι]
    (U : UnitaryTransport H K) (weight : ι → Real) (rho : ι → DensityOperator H)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) (hweight_sum : ∑ i, weight i = 1) :
    U.conjDensity
        (DensityOperator.convexCombination Finset.univ weight rho
          (by intro i _; exact hweight_nonneg i) hweight_sum) =
      DensityOperator.convexCombination Finset.univ weight
        (fun i => U.conjDensity (rho i))
        (by intro i _; exact hweight_nonneg i) hweight_sum := by
  apply densityOperator_ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator]
  simp only [
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  change U.conjOperatorLinearMap (∑ i ∈ Finset.univ,
      (weight i : Complex) • (rho i).toOperator) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rfl
private theorem convexCombination_equiv
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (equiv : ι ≃ κ) (weight : ι → Real)
    (rho : ι → DensityOperator H)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) (hweight_sum : ∑ i, weight i = 1) :
    DensityOperator.convexCombination Finset.univ weight rho
        (by intro i _; exact hweight_nonneg i) hweight_sum =
      DensityOperator.convexCombination Finset.univ
        (fun j => weight (equiv.symm j)) (fun j => rho (equiv.symm j))
        (by intro j _; exact hweight_nonneg (equiv.symm j))
        ((equiv.symm.sum_comp weight).trans hweight_sum) := by
  apply densityOperator_ext_toOperator
  simp only [DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  apply Fintype.sum_equiv equiv
  intro i
  simp
private theorem bk15TensorDensity_noisy_eq_flat (epsilon : BK15Epsilon) :
    bk15TensorDensity (bk15NoisyResources epsilon) =
      (bk15FlatExpansion epsilon).flat := by
  change (bk15FlatExpansion epsilon).physical = (bk15FlatExpansion epsilon).flat
  exact (bk15FlatExpansion epsilon).physical_eq_flat
private theorem bk15FlatExpansion_weight_eq_bk15WordWeight
    (epsilon : BK15Epsilon) (bits : BK15BitTuple) :
    (bk15FlatExpansion epsilon).weight bits =
      bk15WordWeight epsilon (bk15TupleBitstring bits) := by
  rcases bits with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14⟩
  change aInputWeight epsilon b0 *
      (aInputWeight epsilon b1 *
        (aInputWeight epsilon b2 *
          (aInputWeight epsilon b3 *
            (aInputWeight epsilon b4 *
              (aInputWeight epsilon b5 *
                (aInputWeight epsilon b6 *
                  (aInputWeight epsilon b7 *
                    (aInputWeight epsilon b8 *
                      (aInputWeight epsilon b9 *
                        (aInputWeight epsilon b10 *
                          (aInputWeight epsilon b11 *
                            (aInputWeight epsilon b12 *
                              (aInputWeight epsilon b13 *
                                aInputWeight epsilon b14))))))))))))) =
      bk15WordWeight epsilon
        (bk15TupleBitstring
          (b0, (b1, (b2, (b3, (b4, (b5, (b6, (b7, (b8, (b9, (b10,
            (b11, (b12, (b13, b14)))))))))))))))
  unfold bk15WordWeight
  rw [show (Finset.univ : Finset (Fin 15)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} by decide]
  simp [bk15TupleBitstring] <;> ring
private theorem bk15FlatExpansion_component_eq_bk15ErrorWordDensity
    (epsilon : BK15Epsilon) (bits : BK15BitTuple) :
    bk15TensorRegisterTransport.conjDensity
      ((bk15FlatExpansion epsilon).component bits) =
      bk15ErrorWordDensity (bk15TupleBitstring bits) := by
  rcases bits with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14⟩
  rfl
set_option maxHeartbeats 1000000 in
private theorem bk15TensorRegisterTransport_conj_flat_eq_bk15FlatErrorWordMixture
    (epsilon : BK15Epsilon) :
    bk15TensorRegisterTransport.conjDensity ((bk15FlatExpansion epsilon).flat) =
      bk15FlatErrorWordMixture epsilon := by
  calc
    bk15TensorRegisterTransport.conjDensity ((bk15FlatExpansion epsilon).flat) =
        DensityOperator.convexCombination Finset.univ
          (bk15FlatExpansion epsilon).weight
          (fun bits => bk15TensorRegisterTransport.conjDensity
            ((bk15FlatExpansion epsilon).component bits))
          (by
            intro bits _
            exact (bk15FlatExpansion epsilon).nonneg bits)
          (bk15FlatExpansion epsilon).sum_one := by
      unfold FlatExpansion.flat
      exact conjDensity_convexCombination bk15TensorRegisterTransport
        (bk15FlatExpansion epsilon).weight (bk15FlatExpansion epsilon).component
        (bk15FlatExpansion epsilon).nonneg (bk15FlatExpansion epsilon).sum_one
    _ = DensityOperator.convexCombination Finset.univ
          (fun word => (bk15FlatExpansion epsilon).weight
            (bk15BitstringEquiv.symm word))
          (fun word => bk15TensorRegisterTransport.conjDensity
            ((bk15FlatExpansion epsilon).component (bk15BitstringEquiv.symm word)))
          (by
            intro word _
            exact (bk15FlatExpansion epsilon).nonneg (bk15BitstringEquiv.symm word))
          ((bk15BitstringEquiv.symm.sum_comp
            (bk15FlatExpansion epsilon).weight).trans
            (bk15FlatExpansion epsilon).sum_one) :=
      convexCombination_equiv bk15BitstringEquiv
        (bk15FlatExpansion epsilon).weight
        (fun bits => bk15TensorRegisterTransport.conjDensity
          ((bk15FlatExpansion epsilon).component bits))
        (bk15FlatExpansion epsilon).nonneg (bk15FlatExpansion epsilon).sum_one
    _ = bk15FlatErrorWordMixture epsilon := by
      have hweight :
          (fun word => (bk15FlatExpansion epsilon).weight
            (bk15BitstringEquiv.symm word)) = bk15WordWeight epsilon := by
        funext word
        change (bk15FlatExpansion epsilon).weight (splitBK15Bitstring word) =
          bk15WordWeight epsilon word
        simpa using bk15FlatExpansion_weight_eq_bk15WordWeight epsilon
          (splitBK15Bitstring word)
      have hcomponent :
          (fun word => bk15TensorRegisterTransport.conjDensity
            ((bk15FlatExpansion epsilon).component (bk15BitstringEquiv.symm word))) =
          bk15ErrorWordDensity := by
        funext word
        change bk15TensorRegisterTransport.conjDensity
          ((bk15FlatExpansion epsilon).component (splitBK15Bitstring word)) =
          bk15ErrorWordDensity word
        simpa using bk15FlatExpansion_component_eq_bk15ErrorWordDensity epsilon
          (splitBK15Bitstring word)
      unfold bk15FlatErrorWordMixture
      apply densityOperator_ext_toOperator
      simp only [DensityOperator.convexCombination_toOperator]
      unfold DensityOperator.convexCombinationOperator
      apply Finset.sum_congr rfl
      intro word _
      exact congrArg₂ (fun (weight : Complex) (component : Operator BK15Register) =>
        weight • component)
        (congrArg (fun weight : Real => (weight : Complex)) (congrFun hweight word))
        (congrArg DensityOperator.toOperator (congrFun hcomponent word))
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
    (epsilon : BK15Epsilon) :
    bk15PrepareInput (bk15NoisyResources epsilon) = bk15ErrorWordMixture epsilon := by
  unfold bk15PrepareInput bk15ErrorWordMixture bk15FlatErrorWordMixture
  rw [bk15TensorDensity_noisy_eq_flat]
  exact bk15TensorRegisterTransport_conj_flat_eq_bk15FlatErrorWordMixture epsilon
end QEC.Distillation.BK15.NoisyInput
