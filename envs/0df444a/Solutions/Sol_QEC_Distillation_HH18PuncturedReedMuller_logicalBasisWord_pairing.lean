-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:28:19.308609+00:00
-- url     : https://prove2.me/submissions/92af8d7a-23d6-4bb4-9148-5678e181ca29

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_le_dual_of_add_lt
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
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
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
private theorem wordPairing_restrict_split {m w : Nat}
    (left right : Word (ZMod 2) (BooleanPoint m)) :
    wordPairing left right =
      wordPairing (restrictLow m w left) (restrictLow m w right) +
        wordPairing (restrictKept m w left) (restrictKept m w right) := by
  classical
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : BooleanPoint m => pointWeight point ≤ w)
      (fun point => left point * right point)
  let complementKept :
      {point : BooleanPoint m // ¬ pointWeight point ≤ w} ≃ KeptPoint m w :=
    { toFun := fun point => ⟨point.1, by omega⟩
      invFun := fun point => ⟨point.1, by omega⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  have hequiv :
      (∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
        left point.1 * right point.1) =
        ∑ point : KeptPoint m w, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  change
    (∑ point : BooleanPoint m, left point * right point) =
      (∑ point : LowPoint m w, left point.1 * right point.1) +
        ∑ point : KeptPoint m w, left point.1 * right point.1
  calc
    (∑ point : BooleanPoint m, left point * right point) =
        (∑ point : LowPoint m w, left point.1 * right point.1) +
          ∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
            left point.1 * right point.1 := by
      simpa only [LowPoint] using hsplit.symm
    _ = (∑ point : LowPoint m w, left point.1 * right point.1) +
          ∑ point : KeptPoint m w, left point.1 * right point.1 := by
      rw [hequiv]
private theorem wordPairing_systematicKeptLift {w r m : Nat}
    (h : Admissible w r m)
    (left right : Word (ZMod 2) (LogicalSite m w)) :
    wordPairing (keptSystematicLift h left) (keptSystematicLift h right) =
      wordPairing left right := by
  classical
  have hwr : w ≤ r := by
    have hwindow := h.2
    omega
  have hdegree : r + r < m := by
    have hwindow := h.2.2
    omega
  let fullLeft := lowCoordinateExtension hwr left
  let fullRight := lowCoordinateExtension hwr right
  have hfullLeft : fullLeft ∈ (reedMullerCode r m).carrier := by
    simpa [fullLeft] using lowCoordinateExtension_mem_reedMullerCode hwr left
  have hfullRight : fullRight ∈ (reedMullerCode r m).carrier := by
    simpa [fullRight] using lowCoordinateExtension_mem_reedMullerCode hwr right
  have hfullLeftDual : fullLeft ∈ (reedMullerCode r m).dual.carrier :=
    reedMullerCode_le_dual_of_add_lt hdegree hfullLeft
  have hfullPair : wordPairing fullLeft fullRight = 0 :=
    (reedMullerCode r m).orthogonal_of_mem_dual hfullLeftDual hfullRight
  have hlowLeft : restrictLow m w fullLeft = left := by
    simpa [fullLeft] using restrictLow_lowCoordinateExtension hwr left
  have hlowRight : restrictLow m w fullRight = right := by
    simpa [fullRight] using restrictLow_lowCoordinateExtension hwr right
  have hkeptLeft : restrictKept m w fullLeft = keptSystematicLift h left := by
    change restrictKept m w (lowCoordinateExtension hwr left) =
      restrictKept m w (lowCoordinateExtension hwr left)
    rfl
  have hkeptRight : restrictKept m w fullRight = keptSystematicLift h right := by
    change restrictKept m w (lowCoordinateExtension hwr right) =
      restrictKept m w (lowCoordinateExtension hwr right)
    rfl
  have hsplit := wordPairing_restrict_split (w := w) fullLeft fullRight
  rw [hfullPair, hlowLeft, hlowRight, hkeptLeft, hkeptRight] at hsplit
  have hneg := (eq_neg_of_add_eq_zero_left hsplit.symm).symm
  simpa only [ZMod.neg_eq_self_mod_two] using hneg
end HH18PuncturedReedMuller
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18PuncturedReedMuller
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (left right : LogicalSite m w) :
    wordPairing (logicalBasisWord h left) (logicalBasisWord h right) =
      if left = right then 1 else 0 := by
  classical
  rw [logicalBasisWord, logicalBasisWord,
    wordPairing_systematicKeptLift h]
  by_cases hsites : left = right
  · subst right
    simp [canonicalBasisWord, wordPairing_apply]
  · simp [canonicalBasisWord, wordPairing_apply, hsites]
end QEC.Distillation.HH18PuncturedReedMuller
