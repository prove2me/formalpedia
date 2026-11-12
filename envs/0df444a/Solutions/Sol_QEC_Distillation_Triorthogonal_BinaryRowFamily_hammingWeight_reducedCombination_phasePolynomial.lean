-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_reducedCombination_phasePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:28:50.469198+00:00
-- url     : https://prove2.me/submissions/7ffeaab5-3f3c-4748-bd4e-086ac9ffe0eb

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRowIndexList_nodup
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_hammingWeight_reducedCombination_mod8
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_weight_eq
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_pairOverlap_eq
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_hammingWeight_smul_cast8
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_pairOverlap_smul_cast8
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
section
noncomputable section
namespace QEC
namespace Distillation
namespace Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
namespace CliffordCorrectionAtom
end CliffordCorrectionAtom
universe uO uE uC
namespace BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
private theorem wordWeightSum8_reducedRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) :
    wordWeightSum8 (rs.map fun r => c r • R.reducedRow r) =
      R.logicalExponent8 c rs + 2 * R.rowGammaLinear8 c rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons, wordWeightSum8]
      rw [hammingWeight_smul_cast8, R.reducedRow_weight_eq hR r]
      push_cast
      change bitLift8 (c r) *
          ((R.reducedRowParity r : ZMod 8) + 2 * (R.rowGamma r : ZMod 8)) +
          wordWeightSum8 (rs.map fun r => c r • R.reducedRow r) =
        ((R.reducedRowParity r : ZMod 8) * bitLift8 (c r) +
          R.logicalExponent8 c rs) +
        2 * ((R.rowGamma r : ZMod 8) * bitLift8 (c r) +
          R.rowGammaLinear8 c rs)
      rw [ih]
      ring
private theorem headPairSum8_reducedRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (r : R.ReducedRowIndex) (rs : List R.ReducedRowIndex) (hr : r ∉ rs) :
    ((rs.map fun s => c s • R.reducedRow s).map fun y =>
      (pairOverlap (c r • R.reducedRow r) y : ZMod 8)).sum =
      2 * (rs.map fun s => (R.rowPairGamma r s : ZMod 8) *
        bitLift8 (c r) * bitLift8 (c s)).sum := by
  induction rs with
  | nil => simp
  | cons s ss ih =>
      have hrs : r ≠ s := by
        intro hrs
        exact hr (by simp [hrs])
      have hrss : r ∉ ss := by
        intro hmem
        exact hr (by simp [hmem])
      simp only [List.map_cons, List.sum_cons]
      rw [pairOverlap_smul_cast8, R.reducedRow_pairOverlap_eq hR hrs]
      push_cast
      rw [ih hrss]
      ring
private theorem wordPairSum8_reducedRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (rs : List R.ReducedRowIndex) (hnd : rs.Nodup) :
    wordPairSum8 (rs.map fun r => c r • R.reducedRow r) =
      2 * R.rowGammaPair8 c rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
      have hndrs : rs.Nodup := (List.nodup_cons.mp hnd).2
      simp only [List.map_cons, wordPairSum8, rowGammaPair8]
      rw [headPairSum8_reducedRows R hR c r rs hr, ih hndrs]
      ring
universe v
end BinaryRowFamily
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
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    (HammingWeight (R.reducedCombination c) : ZMod 8) =
      R.logicalExponent8 c R.reducedRowIndexList + R.rowCliffordExponent8 c := by
  rw [R.hammingWeight_reducedCombination_mod8 hR]
  change wordWeightSum8
      (R.reducedRowIndexList.map fun r => c r • R.reducedRow r) -
      2 * wordPairSum8
        (R.reducedRowIndexList.map fun r => c r • R.reducedRow r) = _
  rw [wordWeightSum8_reducedRows R hR c,
    wordPairSum8_reducedRows R hR c R.reducedRowIndexList
      R.reducedRowIndexList_nodup]
  simp only [rowCliffordExponent8]
  ring
end QEC.Distillation.Triorthogonal.BinaryRowFamily
