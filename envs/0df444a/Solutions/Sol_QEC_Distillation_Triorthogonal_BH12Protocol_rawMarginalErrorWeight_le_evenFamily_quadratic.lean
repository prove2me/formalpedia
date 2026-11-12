-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_le_evenFamily_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:54:11.287992+00:00
-- url     : https://prove2.me/submissions/e3588a2b-f378-4476-9b2e-3a725fd1c208

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawMarginalErrorWeight_eq_evenFamilyWeightSum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
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
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_coe_extensionCoefficientLinearEquiv_apply
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


section
noncomputable section
namespace QEC
namespace Distillation
namespace Triorthogonal
namespace BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
private theorem one_sub_pow_le_nat_mul_one_sub (r : ℝ) (hr0 : 0 ≤ r) (n : Nat) :
    1 - r ^ n ≤ (n : ℝ) * (1 - r) := by
  have hbernoulli : 1 + (n : ℝ) * (r - 1) ≤ r ^ n := by
    apply one_add_mul_sub_le_pow
    linarith
  linarith
private theorem pow_sub_pow_le_nat_mul_one_sub (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {low high : Nat} (hlow : low ≤ high) :
    r ^ low - r ^ high ≤ ((high - low : Nat) : ℝ) * (1 - r) := by
  have hpow : r ^ high = r ^ low * r ^ (high - low) := by
    calc
      r ^ high = r ^ (low + (high - low)) := by congr 1; omega
      _ = r ^ low * r ^ (high - low) := pow_add r low (high - low)
  rw [hpow]
  calc
    r ^ low - r ^ low * r ^ (high - low) =
        r ^ low * (1 - r ^ (high - low)) := by ring
    _ ≤ 1 * (1 - r ^ (high - low)) := by
      exact mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1)
        (sub_nonneg.mpr (pow_le_one₀ hr0 hr1))
    _ ≤ 1 * ((high - low : Nat) : ℝ) * (1 - r) := by
      simpa only [one_mul] using
        one_sub_pow_le_nat_mul_one_sub r hr0 (high - low)
    _ = ((high - low : Nat) : ℝ) * (1 - r) := by ring
end BH12Protocol
end Triorthogonal
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) (a : OddRow q) (hhalf : p.rate ≤ 1 / 2) :
    rawMarginalErrorWeight q p a ≤
      ((1 + 6 * q : Nat) : ℝ) * p.rate ^ 2 := by
  let r : ℝ := 1 - 2 * p.rate
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith
  have hr1 : r ≤ 1 := by
    dsimp [r]
    linarith [p.rate_nonneg]
  have honeSub : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  have hq : 1 ≤ q := by
    have hlt := a.1.isLt
    omega
  have hhigh : 7 ≤ 3 + 4 * q := by omega
  have hgeom :
      (∑ i ∈ Finset.range 7, r ^ i) * (1 - r) = 1 - r ^ 7 :=
    geom_sum_mul_of_le_one hr1 7
  have hfactor :
      1 + r ^ 8 + 6 * r ^ (4 + 4 * q) - 2 * r ^ 7 -
          6 * r ^ (3 + 4 * q) =
        (1 - r) *
          ((∑ i ∈ Finset.range 7, r ^ i) - r ^ 7 -
            6 * r ^ (3 + 4 * q)) := by
    have hpow : r ^ (4 + 4 * q) = r ^ (3 + 4 * q) * r := by
      rw [show 4 + 4 * q = (3 + 4 * q) + 1 by omega, pow_succ]
    calc
      1 + r ^ 8 + 6 * r ^ (4 + 4 * q) - 2 * r ^ 7 -
          6 * r ^ (3 + 4 * q) =
          (1 - r ^ 7) - r ^ 7 * (1 - r) -
            6 * r ^ (3 + 4 * q) * (1 - r) := by
          rw [hpow]
          ring
      _ = (1 - r) *
          ((∑ i ∈ Finset.range 7, r ^ i) - r ^ 7 -
            6 * r ^ (3 + 4 * q)) := by
          rw [← hgeom]
          ring
  have hfirst :
      (∑ i ∈ Finset.range 7, (r ^ i - r ^ 7)) ≤ 28 * (1 - r) := by
    calc
      (∑ i ∈ Finset.range 7, (r ^ i - r ^ 7)) ≤
          ∑ i ∈ Finset.range 7, ((7 - i : Nat) : ℝ) * (1 - r) := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_sub_pow_le_nat_mul_one_sub r hr0 hr1
          (Nat.le_of_lt (Finset.mem_range.mp hi))
      _ = 28 * (1 - r) := by
        norm_num [Finset.sum_range_succ]
        ring
  have hsecond : r ^ 7 - r ^ (3 + 4 * q) ≤
      ((3 + 4 * q - 7 : Nat) : ℝ) * (1 - r) :=
    pow_sub_pow_le_nat_mul_one_sub r hr0 hr1 hhigh
  have hbracket :
      (∑ i ∈ Finset.range 7, r ^ i) - r ^ 7 -
          6 * r ^ (3 + 4 * q) ≤
        ((4 + 24 * q : Nat) : ℝ) * (1 - r) := by
    calc
      (∑ i ∈ Finset.range 7, r ^ i) - r ^ 7 -
          6 * r ^ (3 + 4 * q) =
          (∑ i ∈ Finset.range 7, (r ^ i - r ^ 7)) +
            6 * (r ^ 7 - r ^ (3 + 4 * q)) := by
          norm_num [Finset.sum_range_succ]
          ring
      _ ≤ 28 * (1 - r) +
          6 * (((3 + 4 * q - 7 : Nat) : ℝ) * (1 - r)) := by
          exact add_le_add hfirst
            (mul_le_mul_of_nonneg_left hsecond (by norm_num))
      _ = ((4 + 24 * q : Nat) : ℝ) * (1 - r) := by
          rw [Nat.cast_sub hhigh]
          push_cast
          ring
  rw [rawMarginalErrorWeight_eq_evenFamilyWeightSum]
  change (16 : ℝ)⁻¹ *
      (1 + r ^ 8 + 6 * r ^ (4 + 4 * q) - 2 * r ^ 7 -
        6 * r ^ (3 + 4 * q)) ≤
    ((1 + 6 * q : Nat) : ℝ) * p.rate ^ 2
  calc
    (16 : ℝ)⁻¹ *
        (1 + r ^ 8 + 6 * r ^ (4 + 4 * q) - 2 * r ^ 7 -
          6 * r ^ (3 + 4 * q)) =
        (16 : ℝ)⁻¹ * ((1 - r) *
          ((∑ i ∈ Finset.range 7, r ^ i) - r ^ 7 -
            6 * r ^ (3 + 4 * q))) := by rw [hfactor]
    _ ≤ (16 : ℝ)⁻¹ * ((1 - r) *
          (((4 + 24 * q : Nat) : ℝ) * (1 - r))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hbracket honeSub) (by norm_num)
    _ = ((1 + 6 * q : Nat) : ℝ) * p.rate ^ 2 := by
          dsimp [r]
          push_cast
          ring
end QEC.Distillation.Triorthogonal.BH12Protocol
