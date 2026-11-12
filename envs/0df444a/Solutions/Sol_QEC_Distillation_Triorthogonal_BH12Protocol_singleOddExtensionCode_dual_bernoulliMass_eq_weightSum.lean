-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.singleOddExtensionCode_dual_bernoulliMass_eq_weightSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:46:17.491218+00:00
-- url     : https://prove2.me/submissions/ce306722-3353-428b-aa6c-1b8f47a57d6d

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
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
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
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
private theorem binaryCodeCharacter_translate {q : Nat}
    (C : LinearCode (ZMod 2) (Column q)) (word codeword : C.carrier)
    (error : PhysicalError q)
    (hword : wordPairing (word : PhysicalError q) error ≠ 0) :
    binaryCodeCharacter C (binaryCodeTranslate C word codeword) error =
      -binaryCodeCharacter C codeword error := by
  unfold binaryCodeCharacter
  change realBinarySign
      (wordPairing ((codeword : PhysicalError q) + (word : PhysicalError q)) error) = _
  rw [map_add]
  exact realBinarySign_add_of_ne_zero _ _ hword
private theorem binaryCodeCharacter_sum (q : Nat)
    (C : LinearCode (ZMod 2) (Column q)) (error : PhysicalError q) :
    (∑ codeword : C.carrier, binaryCodeCharacter C codeword error) =
      if error ∈ C.dual.carrier then binaryCodeCarrierCard C else 0 := by
  classical
  letI : Fintype C.carrier := Fintype.ofFinite _
  unfold binaryCodeCarrierCard
  by_cases hdual : error ∈ C.dual.carrier
  · have horth (codeword : C.carrier) :
        wordPairing (codeword : PhysicalError q) error = 0 :=
      LinearCode.dual_orthogonal C codeword.property hdual
    rw [if_pos hdual]
    simp [binaryCodeCharacter, realBinarySign, horth]
  · obtain ⟨word, hword, hpair⟩ :=
      exists_carrier_wordPairing_ne_zero_of_not_mem_dual C hdual
    let carrierWord : C.carrier := ⟨word, hword⟩
    have hpair' : wordPairing (carrierWord : PhysicalError q) error ≠ 0 := by
      simpa [wordPairing_apply, dotProduct_comm] using hpair
    have htranslate :
        (∑ codeword : C.carrier, binaryCodeCharacter C codeword error) =
          ∑ codeword : C.carrier,
            binaryCodeCharacter C (binaryCodeTranslate C carrierWord codeword) error := by
      symm
      exact (binaryCodeTranslate C carrierWord).sum_comp
        (fun codeword => binaryCodeCharacter C codeword error)
    rw [if_neg hdual]
    have hneg :
        (∑ codeword : C.carrier, binaryCodeCharacter C codeword error) =
          -(∑ codeword : C.carrier, binaryCodeCharacter C codeword error) := by
      calc
        (∑ codeword : C.carrier, binaryCodeCharacter C codeword error) =
            ∑ codeword : C.carrier,
              binaryCodeCharacter C (binaryCodeTranslate C carrierWord codeword) error :=
          htranslate
        _ = ∑ codeword : C.carrier, -binaryCodeCharacter C codeword error := by
          apply Finset.sum_congr rfl
          intro codeword _
          exact binaryCodeCharacter_translate C carrierWord codeword error hpair'
        _ = -(∑ codeword : C.carrier, binaryCodeCharacter C codeword error) := by
          rw [Finset.sum_neg_distrib]
    simpa using (CharZero.eq_neg_self_iff.mp hneg)
private theorem binaryCode_dual_indicator_eq_character_average (q : Nat)
    (C : LinearCode (ZMod 2) (Column q)) (error : PhysicalError q) :
    (if error ∈ C.dual.carrier then (1 : ℝ) else 0) =
      (binaryCodeCarrierCard C : ℝ)⁻¹ *
        ∑ codeword : C.carrier, binaryCodeCharacter C codeword error := by
  have hcard : (binaryCodeCarrierCard C : ℝ) ≠ 0 := by
    unfold binaryCodeCarrierCard
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card C.carrier ≠ 0)
  rw [binaryCodeCharacter_sum]
  by_cases hdual : error ∈ C.dual.carrier <;>
    simp only [hdual, if_true, if_false, Nat.cast_zero, mul_zero, inv_mul_cancel₀ hcard]
private theorem binaryLinearCode_dual_bernoulliMass_eq_weightSum (q : Nat)
    (C : LinearCode (ZMod 2) (Column q)) (p : ErrorParameter) :
    (∑ error : C.dual.carrier,
      errorWordProbability p (error : PhysicalError q)) =
      (binaryCodeCarrierCard C : ℝ)⁻¹ *
        codeWeightSum C (fun weight => (1 - 2 * p.rate) ^ weight) := by
  classical
  letI : Fintype C.carrier := Fintype.ofFinite _
  calc
    (∑ error : C.dual.carrier,
      errorWordProbability p (error : PhysicalError q)) =
        ∑ error : PhysicalError q,
          if herror : error ∈ C.dual.carrier then
            errorWordProbability p error else 0 := by
      symm
      simpa using sum_dite_submodule_real C.dual.carrier
        (fun error => errorWordProbability p (error : PhysicalError q))
    _ = ∑ error : PhysicalError q,
          errorWordProbability p error *
            (if error ∈ C.dual.carrier then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro error _
      by_cases hdual : error ∈ C.dual.carrier <;>
        simp only [hdual, dite_true, dite_false, if_true, if_false, mul_one, mul_zero]
    _ = ∑ error : PhysicalError q,
          errorWordProbability p error *
            ((binaryCodeCarrierCard C : ℝ)⁻¹ *
              ∑ codeword : C.carrier, binaryCodeCharacter C codeword error) := by
      apply Finset.sum_congr rfl
      intro error _
      exact congrArg (errorWordProbability p error * ·)
        (binaryCode_dual_indicator_eq_character_average q C error)
    _ = (binaryCodeCarrierCard C : ℝ)⁻¹ *
          ∑ codeword : C.carrier,
            ∑ error : PhysicalError q,
              errorWordProbability p error * binaryCodeCharacter C codeword error := by
      calc
        (∑ error : PhysicalError q,
          errorWordProbability p error *
            ((binaryCodeCarrierCard C : ℝ)⁻¹ *
              ∑ codeword : C.carrier, binaryCodeCharacter C codeword error)) =
            ∑ error : PhysicalError q,
              ∑ codeword : C.carrier,
                (binaryCodeCarrierCard C : ℝ)⁻¹ *
                  (errorWordProbability p error * binaryCodeCharacter C codeword error) := by
              apply Finset.sum_congr rfl
              intro error _
              calc
                errorWordProbability p error *
                    ((binaryCodeCarrierCard C : ℝ)⁻¹ *
                      ∑ codeword : C.carrier, binaryCodeCharacter C codeword error) =
                    (binaryCodeCarrierCard C : ℝ)⁻¹ *
                      (errorWordProbability p error *
                        ∑ codeword : C.carrier, binaryCodeCharacter C codeword error) := by
                  ring
                _ = (binaryCodeCarrierCard C : ℝ)⁻¹ *
                      ∑ codeword : C.carrier,
                        errorWordProbability p error * binaryCodeCharacter C codeword error := by
                  rw [Finset.mul_sum]
                _ = ∑ codeword : C.carrier,
                      (binaryCodeCarrierCard C : ℝ)⁻¹ *
                        (errorWordProbability p error * binaryCodeCharacter C codeword error) := by
                  rw [Finset.mul_sum]
        _ = (binaryCodeCarrierCard C : ℝ)⁻¹ *
            ∑ codeword : C.carrier,
              ∑ error : PhysicalError q,
                errorWordProbability p error * binaryCodeCharacter C codeword error := by
              rw [Finset.sum_comm, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro codeword _
              rw [Finset.mul_sum]
    _ = (binaryCodeCarrierCard C : ℝ)⁻¹ *
          ∑ codeword : C.carrier,
            (1 - 2 * p.rate) ^ HammingWeight (codeword : PhysicalError q) := by
      apply congrArg ((binaryCodeCarrierCard C : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro codeword _
      simpa [binaryCodeCharacter] using
        bernoulliCharacter_transform q p (codeword : PhysicalError q)
    _ = (binaryCodeCarrierCard C : ℝ)⁻¹ *
          codeWeightSum C (fun weight => (1 - 2 * p.rate) ^ weight) := by
      apply congrArg ((binaryCodeCarrierCard C : ℝ)⁻¹ * ·)
      unfold codeWeightSum
      apply Finset.sum_congr
      · ext codeword
        simp
      · intro codeword _
        rfl
private theorem singleOddExtensionCode_carrier_card {q : Nat} (a : OddRow q) :
    binaryCodeCarrierCard (singleOddExtensionCode a) = 16 := by
  unfold binaryCodeCarrierCard
  letI : Fintype (singleOddExtensionCode a).carrier := Fintype.ofFinite _
  calc
    Fintype.card (singleOddExtensionCode a).carrier =
        Fintype.card (Sum Unit EvenRow → ZMod 2) :=
      Fintype.card_congr (extensionCoefficientLinearEquiv a).toEquiv.symm
    _ = Fintype.card (ZMod 2 × Fin 8) :=
      Fintype.card_congr extensionCoefficientEquiv.symm
    _ = 16 := by decide +kernel
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
    (a : OddRow q) (p : ErrorParameter) :
    (∑ error : (singleOddExtensionCode a).dual.carrier,
      errorWordProbability p (error : PhysicalError q)) =
      (16 : ℝ)⁻¹ *
        codeWeightSum (singleOddExtensionCode a)
          (fun weight => (1 - 2 * p.rate) ^ weight) := by
  rw [binaryLinearCode_dual_bernoulliMass_eq_weightSum,
    singleOddExtensionCode_carrier_card]
  norm_num
end QEC.Distillation.Triorthogonal.BH12Protocol
