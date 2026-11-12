-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.hammingWeight_wordListXor_mod8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:53:33.680731+00:00
-- url     : https://prove2.me/submissions/37e17329-bc74-4f9a-869c-6403bb6aff9e

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_bitLift8_booleanXor
import Theorems.Thm_QEC_Distillation_Triorthogonal_hammingWeight_cast8
import Theorems.Thm_QEC_Distillation_Triorthogonal_pairOverlap_cast8
import Theorems.Thm_QEC_Distillation_Triorthogonal_tripleOverlap_cast8
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
private theorem elementaryOne_eq_weightSum8
    (xs : List (Word (ZMod 2) Index)) :
    wordElementaryOne8 xs = wordWeightSum8 xs := by
  induction xs with
  | nil => simp [wordElementaryOne8, wordWeightSum8, booleanElementaryOne]
  | cons x xs ih =>
      simp only [wordElementaryOne8, List.map_cons, booleanElementaryOne,
        Finset.sum_add_distrib]
      rw [← hammingWeight_cast8]
      change (HammingWeight x : ZMod 8) + wordElementaryOne8 xs =
        wordWeightSum8 (x :: xs)
      rw [ih]
      rfl
private theorem headElementaryOne_eq_pairSum
    (x : Word (ZMod 2) Index) (xs : List (Word (ZMod 2) Index)) :
    (∑ p, bitLift8 (x p) * booleanElementaryOne (xs.map fun y => y p)) =
      (xs.map fun y => (BinaryRowFamily.pairOverlap x y : ZMod 8)).sum := by
  induction xs with
  | nil => simp [booleanElementaryOne]
  | cons y ys ih =>
      simp only [List.map_cons, booleanElementaryOne, mul_add, Finset.sum_add_distrib,
        List.sum_cons]
      rw [← pairOverlap_cast8, ih]
private theorem elementaryTwo_eq_pairSum8
    (xs : List (Word (ZMod 2) Index)) :
    wordElementaryTwo8 xs = wordPairSum8 xs := by
  induction xs with
  | nil => simp [wordElementaryTwo8, wordPairSum8, booleanElementaryTwo]
  | cons x xs ih =>
      simp only [wordElementaryTwo8, List.map_cons, booleanElementaryTwo,
        Finset.sum_add_distrib]
      rw [headElementaryOne_eq_pairSum]
      change (xs.map fun y => (BinaryRowFamily.pairOverlap x y : ZMod 8)).sum +
        wordElementaryTwo8 xs = wordPairSum8 (x :: xs)
      rw [ih]
      rfl
private theorem fixedTwoElementaryOne_eq_tripleSum
    (x y : Word (ZMod 2) Index) (xs : List (Word (ZMod 2) Index)) :
    (∑ p, bitLift8 (x p) * bitLift8 (y p) *
      booleanElementaryOne (xs.map fun z => z p)) =
      fixedPairTripleSum8 x y xs := by
  induction xs with
  | nil => simp [booleanElementaryOne, fixedPairTripleSum8]
  | cons z zs ih =>
      simp only [List.map_cons, booleanElementaryOne, mul_add, Finset.sum_add_distrib,
        fixedPairTripleSum8]
      rw [← tripleOverlap_cast8, ih]
private theorem headElementaryTwo_eq_tripleSum
    (x : Word (ZMod 2) Index) (xs : List (Word (ZMod 2) Index)) :
    (∑ p, bitLift8 (x p) * booleanElementaryTwo (xs.map fun y => y p)) =
      fixedTripleSum8 x xs := by
  induction xs with
  | nil => simp [booleanElementaryTwo, fixedTripleSum8]
  | cons y ys ih =>
      simp only [List.map_cons, booleanElementaryTwo, mul_add, Finset.sum_add_distrib,
        fixedTripleSum8]
      simp_rw [← mul_assoc]
      rw [fixedTwoElementaryOne_eq_tripleSum, ih]
private theorem elementaryThree_eq_tripleSum8
    (xs : List (Word (ZMod 2) Index)) :
    wordElementaryThree8 xs = wordTripleSum8 xs := by
  induction xs with
  | nil => simp [wordElementaryThree8, wordTripleSum8, booleanElementaryThree]
  | cons x xs ih =>
      simp only [wordElementaryThree8, List.map_cons, booleanElementaryThree,
        Finset.sum_add_distrib]
      rw [headElementaryTwo_eq_tripleSum]
      change fixedTripleSum8 x xs + wordElementaryThree8 xs =
        wordTripleSum8 (x :: xs)
      rw [ih]
      rfl
namespace CliffordCorrectionAtom
end CliffordCorrectionAtom
universe uO uE uC
namespace BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
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
namespace QEC.Distillation.Triorthogonal
theorem _root_.solution
    (xs : List (Word (ZMod 2) Index)) :
    (HammingWeight (wordListXor xs) : ZMod 8) =
      wordWeightSum8 xs - 2 * wordPairSum8 xs + 4 * wordTripleSum8 xs := by
  rw [hammingWeight_cast8]
  calc
    ∑ p, bitLift8 (wordListXor xs p) =
        ∑ p, (booleanElementaryOne (xs.map fun x => x p) -
          2 * booleanElementaryTwo (xs.map fun x => x p) +
          4 * booleanElementaryThree (xs.map fun x => x p)) := by
            apply Finset.sum_congr rfl
            intro p _hp
            rw [wordListXor_apply, bitLift8_booleanXor]
    _ = wordElementaryOne8 xs - 2 * wordElementaryTwo8 xs +
        4 * wordElementaryThree8 xs := by
          simp only [wordElementaryOne8, wordElementaryTwo8, wordElementaryThree8]
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.mul_sum]
    _ = wordWeightSum8 xs - 2 * wordPairSum8 xs + 4 * wordTripleSum8 xs := by
          rw [elementaryOne_eq_weightSum8, elementaryTwo_eq_pairSum8,
            elementaryThree_eq_tripleSum8]
end QEC.Distillation.Triorthogonal
