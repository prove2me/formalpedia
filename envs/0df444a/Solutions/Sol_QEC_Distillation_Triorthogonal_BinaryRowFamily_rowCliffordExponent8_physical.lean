-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCliffordExponent8_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:17:19.960311+00:00
-- url     : https://prove2.me/submissions/1bce109a-1341-44a4-931a-e7ec48ca350a

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_two_mul_bitLift8_booleanXor
import Theorems.Thm_QEC_Distillation_Triorthogonal_four_mul_bitLift8_booleanXor_mul
import Theorems.Thm_QEC_Distillation_Triorthogonal_unorderedPairs_map
import Theorems.Thm_QEC_Distillation_Triorthogonal_bitPairSum8_eq_unorderedPairs
import Theorems.Thm_QEC_Distillation_Triorthogonal_list_sum_mul_sum_split_pairs
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_booleanXor_coefficientBitList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
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
private theorem mul_list_sum {R : Type*} [Semiring R] (a : R) (xs : List R) :
    a * xs.sum = (xs.map fun x => a * x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]
private theorem list_sum_map_add {A R : Type*} [AddCommMonoid R]
    (xs : List A) (f g : A → R) :
    (xs.map fun x => f x + g x).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc, add_left_comm]
private theorem list_sum_comm {A B R : Type*} [AddCommMonoid R]
    (xs : List A) (ys : List B) (f : A → B → R) :
    (xs.map fun x => (ys.map fun y => f x y).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, list_sum_map_add]
private theorem list_sum_map_mul_right {A R : Type*} [Semiring R]
    (xs : List A) (f : A → R) (a : R) :
    (xs.map fun x => f x * a).sum = (xs.map f).sum * a := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_mul]
private theorem list_sum_map_sub {A R : Type*} [AddCommGroup R]
    (xs : List A) (f g : A → R) :
    (xs.map fun x => f x - g x).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      abel
universe uO uE uC
namespace BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
private theorem lambdaSingle8_cast4
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) :
    ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) (R.lambdaSingle8 p) =
      R.lambdaSingle p := by
  let phi : ZMod 8 →+* ZMod 4 := ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)
  have hbit (b : ZMod 2) : phi (bitLift8 b) = bitLift4 b := by
    fin_cases b <;> decide
  have hlinear :
      ((R.reducedRowIndexList.map fun r => (R.rowGamma r : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry r p)).map phi).sum =
        (R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 4) * bitLift4 (R.rowCoefficientEntry r p)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _hr
    simp [Function.comp_apply, hbit]
  have hquadratic :
      (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).map phi).sum =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 4) *
            bitLift4 (R.rowCoefficientEntry rs.1 p) *
              bitLift4 (R.rowCoefficientEntry rs.2 p)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro rs _hrs
    simp [Function.comp_apply, hbit]
  change phi
      ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p)).sum -
        2 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).sum) = _
  rw [map_sub, map_mul,
    map_list_sum phi
      (R.reducedRowIndexList.map fun r =>
        (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p)),
    map_list_sum phi
      ((unorderedPairs R.reducedRowIndexList).map fun rs =>
        (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry rs.1 p) *
            bitLift8 (R.rowCoefficientEntry rs.2 p))]
  rw [hlinear, hquadratic]
  simp [lambdaSingle]
  rw [show phi 2 = (2 : ZMod 4) by decide]
private theorem lambdaPair8_cast2
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) :
    ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (R.lambdaPair8 p q) =
      R.lambdaPair p q := by
  let phi : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
  have hbit (b : ZMod 2) : phi (bitLift8 b) = b := by
    change phi (b.val : ZMod 8) = b
    rw [map_natCast]
    exact ZMod.natCast_zmod_val b
  have hlinear :
      ((R.reducedRowIndexList.map fun r => (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r p) *
              bitLift8 (R.rowCoefficientEntry r q)).map phi).sum =
        (R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 2) * R.rowCoefficientEntry r p *
            R.rowCoefficientEntry r q).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _hr
    simp [Function.comp_apply, hbit]
  have hquadratic :
      (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 q) +
              bitLift8 (R.rowCoefficientEntry rs.2 p) *
                bitLift8 (R.rowCoefficientEntry rs.1 q))).map phi).sum =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 2) *
            (R.rowCoefficientEntry rs.1 p * R.rowCoefficientEntry rs.2 q +
              R.rowCoefficientEntry rs.2 p * R.rowCoefficientEntry rs.1 q)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro rs _hrs
    simp [Function.comp_apply, hbit]
  change phi
      ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p) *
            bitLift8 (R.rowCoefficientEntry r q)).sum -
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 q) +
              bitLift8 (R.rowCoefficientEntry rs.2 p) *
                bitLift8 (R.rowCoefficientEntry rs.1 q))).sum) = _
  rw [map_sub,
    map_list_sum phi
      (R.reducedRowIndexList.map fun r =>
        (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p) *
          bitLift8 (R.rowCoefficientEntry r q)),
    map_list_sum phi
      ((unorderedPairs R.reducedRowIndexList).map fun rs =>
        (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          (bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 q) +
            bitLift8 (R.rowCoefficientEntry rs.2 p) *
              bitLift8 (R.rowCoefficientEntry rs.1 q)))]
  rw [hlinear, hquadratic]
  simp [lambdaPair]
private theorem two_mul_eq_val4_of_cast_eq
    (x : ZMod 8) (y : ZMod 4)
    (h : ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) x = y) :
    2 * x = 2 * (y.val : ZMod 8) := by
  subst y
  fin_cases x <;> decide
private theorem four_mul_eq_val2_of_cast_eq
    (x : ZMod 8) (y : ZMod 2)
    (h : ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) x = y) :
    4 * x = 4 * (y.val : ZMod 8) := by
  subst y
  fin_cases x <;> decide
private theorem two_mul_lambdaSingle8
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) :
    2 * R.lambdaSingle8 p = 2 * ((R.lambdaSingle p).val : ZMod 8) :=
  two_mul_eq_val4_of_cast_eq _ _ (R.lambdaSingle8_cast4 p)
private theorem four_mul_lambdaPair8
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) :
    4 * R.lambdaPair8 p q = 4 * ((R.lambdaPair p q).val : ZMod 8) :=
  four_mul_eq_val2_of_cast_eq _ _ (R.lambdaPair8_cast2 p q)
private theorem rowGammaPair8_eq_unorderedPairs
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) :
    R.rowGammaPair8 c rs =
      ((unorderedPairs rs).map fun pq =>
        (R.rowPairGamma pq.1 pq.2 : ZMod 8) *
          bitLift8 (c pq.1) * bitLift8 (c pq.2)).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [rowGammaPair8, unorderedPairs, List.map_append, List.sum_append,
        List.map_map, ih]
      rfl
private theorem coefficientBitList_liftSum8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    ((R.coefficientBitList f r).map bitLift8).sum =
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum := by
  simp only [coefficientBitList, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _hp
  simpa only [Function.comp_apply] using
    bitLift8_mul (R.rowCoefficientEntry r p) (f p)
private theorem coefficientBitList_pairSum8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    bitPairSum8 (R.coefficientBitList f r) =
      ((sitePairList Col).map fun pq =>
        (bitLift8 (R.rowCoefficientEntry r pq.1) * bitLift8 (f pq.1)) *
          (bitLift8 (R.rowCoefficientEntry r pq.2) * bitLift8 (f pq.2))).sum := by
  rw [bitPairSum8_eq_unorderedPairs]
  simp only [coefficientBitList, unorderedPairs_map, sitePairList, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pq _hpq
  change bitLift8 (R.rowCoefficientEntry r pq.1 * f pq.1) *
      bitLift8 (R.rowCoefficientEntry r pq.2 * f pq.2) = _
  rw [bitLift8_mul, bitLift8_mul]
private theorem linearCoordinate_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r) =
      2 * (R.rowGamma r : ZMod 8) *
          ((siteList Col).map fun p =>
            bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum -
        4 * (R.rowGamma r : ZMod 8) *
          ((sitePairList Col).map fun pq =>
            (bitLift8 (R.rowCoefficientEntry r pq.1) * bitLift8 (f pq.1)) *
              (bitLift8 (R.rowCoefficientEntry r pq.2) *
                bitLift8 (f pq.2))).sum := by
  rw [← R.booleanXor_coefficientBitList f r]
  rw [show 2 * (R.rowGamma r : ZMod 8) *
      bitLift8 (booleanXor (R.coefficientBitList f r)) =
      (R.rowGamma r : ZMod 8) *
        (2 * bitLift8 (booleanXor (R.coefficientBitList f r))) by ring]
  rw [two_mul_bitLift8_booleanXor, R.coefficientBitList_liftSum8 f r,
    R.coefficientBitList_pairSum8 f r]
  ring
private theorem quadraticCoordinate_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r s : R.ReducedRowIndex) :
    4 * bitLift8 (R.rowCoefficientMap f r) *
        bitLift8 (R.rowCoefficientMap f s) =
      4 * ((siteList Col).map fun p =>
        (bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)) *
          (bitLift8 (R.rowCoefficientEntry s p) * bitLift8 (f p))).sum +
      4 * ((sitePairList Col).map fun pq =>
        (bitLift8 (R.rowCoefficientEntry r pq.1) * bitLift8 (f pq.1)) *
            (bitLift8 (R.rowCoefficientEntry s pq.2) * bitLift8 (f pq.2)) +
          (bitLift8 (R.rowCoefficientEntry r pq.2) * bitLift8 (f pq.2)) *
            (bitLift8 (R.rowCoefficientEntry s pq.1) * bitLift8 (f pq.1))).sum := by
  rw [← R.booleanXor_coefficientBitList f r,
    ← R.booleanXor_coefficientBitList f s,
    four_mul_bitLift8_booleanXor_mul,
    R.coefficientBitList_liftSum8 f r,
    R.coefficientBitList_liftSum8 f s]
  rw [show 4 *
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum *
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry s p) * bitLift8 (f p)).sum =
      4 * (((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum *
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry s p) * bitLift8 (f p)).sum) by ring]
  rw [list_sum_mul_sum_split_pairs, mul_add]
  simp only [sitePairList]
private theorem linearCoordinate_expand8_siteSums
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r) =
      ((siteList Col).map fun p =>
        2 * (R.rowGamma r : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum -
      ((sitePairList Col).map fun pq =>
        4 * (R.rowGamma r : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry r pq.1) *
            bitLift8 (R.rowCoefficientEntry r pq.2) *
              bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  rw [R.linearCoordinate_expand8 f r]
  rw [mul_list_sum, mul_list_sum]
  apply congrArg₂ (· - ·)
  · rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    simp only [Function.comp_apply]
    ring
  · rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pq _hpq
    simp only [Function.comp_apply]
    ring
private theorem linearCoordinates_sum_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    (R.reducedRowIndexList.map fun r =>
      2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r)).sum =
      2 * ((siteList Col).map fun p =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r p)).sum) * bitLift8 (f p)).sum -
      4 * ((sitePairList Col).map fun pq =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r pq.1) *
              bitLift8 (R.rowCoefficientEntry r pq.2)).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  calc
    (R.reducedRowIndexList.map fun r =>
        2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r)).sum =
        (R.reducedRowIndexList.map fun r =>
          ((siteList Col).map fun p =>
            2 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum -
          ((sitePairList Col).map fun pq =>
            4 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r pq.1) *
                bitLift8 (R.rowCoefficientEntry r pq.2) *
                  bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro r _hr
            exact R.linearCoordinate_expand8_siteSums f r
    _ = ((siteList Col).map fun p =>
          (R.reducedRowIndexList.map fun r =>
            2 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum).sum -
        ((sitePairList Col).map fun pq =>
          (R.reducedRowIndexList.map fun r =>
            4 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r pq.1) *
                bitLift8 (R.rowCoefficientEntry r pq.2) *
                  bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            rw [list_sum_map_sub,
              list_sum_comm R.reducedRowIndexList (siteList Col),
              list_sum_comm R.reducedRowIndexList (sitePairList Col)]
    _ = _ := by
      apply congrArg₂ (· - ·)
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro p _hp
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right]
        have hscale :
            (R.reducedRowIndexList.map fun r =>
              2 * (R.rowGamma r : ZMod 8) *
                bitLift8 (R.rowCoefficientEntry r p)).sum =
              2 * (R.reducedRowIndexList.map fun r =>
                (R.rowGamma r : ZMod 8) *
                  bitLift8 (R.rowCoefficientEntry r p)).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r _hr
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro pq _hpq
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right, list_sum_map_mul_right]
        have hscale :
            (R.reducedRowIndexList.map fun r =>
              4 * (R.rowGamma r : ZMod 8) *
                bitLift8 (R.rowCoefficientEntry r pq.1) *
                  bitLift8 (R.rowCoefficientEntry r pq.2)).sum =
              4 * (R.reducedRowIndexList.map fun r =>
                (R.rowGamma r : ZMod 8) *
                  bitLift8 (R.rowCoefficientEntry r pq.1) *
                    bitLift8 (R.rowCoefficientEntry r pq.2)).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r _hr
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring
private theorem quadraticCoordinate_expand8_siteSums
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (rs : R.ReducedRowIndex × R.ReducedRowIndex) :
    4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientMap f rs.1) *
          bitLift8 (R.rowCoefficientMap f rs.2) =
      ((siteList Col).map fun p =>
        4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry rs.1 p) *
            bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p)).sum +
      ((sitePairList Col).map fun pq =>
        4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
              bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
            bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
              bitLift8 (R.rowCoefficientEntry rs.1 pq.2)) *
            bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  calc
    4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientMap f rs.1) *
          bitLift8 (R.rowCoefficientMap f rs.2) =
        (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          (4 * bitLift8 (R.rowCoefficientMap f rs.1) *
            bitLift8 (R.rowCoefficientMap f rs.2)) := by ring
    _ = (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        (4 * ((siteList Col).map fun p =>
          (bitLift8 (R.rowCoefficientEntry rs.1 p) * bitLift8 (f p)) *
            (bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p))).sum +
        4 * ((sitePairList Col).map fun pq =>
          (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) * bitLift8 (f pq.1)) *
              (bitLift8 (R.rowCoefficientEntry rs.2 pq.2) * bitLift8 (f pq.2)) +
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.2) * bitLift8 (f pq.2)) *
              (bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                bitLift8 (f pq.1))).sum) := by
          rw [R.quadraticCoordinate_expand8 f rs.1 rs.2]
    _ = (4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8)) *
          ((siteList Col).map fun p =>
            (bitLift8 (R.rowCoefficientEntry rs.1 p) * bitLift8 (f p)) *
              (bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p))).sum +
        (4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8)) *
          ((sitePairList Col).map fun pq =>
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) * bitLift8 (f pq.1)) *
                (bitLift8 (R.rowCoefficientEntry rs.2 pq.2) * bitLift8 (f pq.2)) +
              (bitLift8 (R.rowCoefficientEntry rs.1 pq.2) * bitLift8 (f pq.2)) *
                (bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                  bitLift8 (f pq.1))).sum := by ring
    _ = _ := by
      rw [mul_list_sum, mul_list_sum, List.map_map, List.map_map]
      apply congrArg₂ (· + ·)
      · apply congrArg List.sum
        apply List.map_congr_left
        intro p _hp
        simp only [Function.comp_apply]
        ring_nf
        simp only [pow_two, bitLift8_mul_self]
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pq _hpq
        simp only [Function.comp_apply]
        ring
private theorem quadraticCoordinates_sum_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientMap f rs.1) *
          bitLift8 (R.rowCoefficientMap f rs.2)).sum =
      4 * ((siteList Col).map fun p =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).sum) * bitLift8 (f p)).sum +
      4 * ((sitePairList Col).map fun pq =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
              bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  calc
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
        4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          bitLift8 (R.rowCoefficientMap f rs.1) *
            bitLift8 (R.rowCoefficientMap f rs.2)).sum =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          ((siteList Col).map fun p =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p)).sum +
          ((sitePairList Col).map fun pq =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.1 pq.2)) *
                bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro rs _hrs
            exact R.quadraticCoordinate_expand8_siteSums f rs
    _ = ((siteList Col).map fun p =>
          ((unorderedPairs R.reducedRowIndexList).map fun rs =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p)).sum).sum +
        ((sitePairList Col).map fun pq =>
          ((unorderedPairs R.reducedRowIndexList).map fun rs =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.1 pq.2)) *
                bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            rw [list_sum_map_add,
              list_sum_comm (unorderedPairs R.reducedRowIndexList) (siteList Col),
              list_sum_comm (unorderedPairs R.reducedRowIndexList)
                (sitePairList Col)]
    _ = _ := by
      apply congrArg₂ (· + ·)
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro p _hp
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right]
        have hscale :
            ((unorderedPairs R.reducedRowIndexList).map fun rs =>
              4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                bitLift8 (R.rowCoefficientEntry rs.1 p) *
                  bitLift8 (R.rowCoefficientEntry rs.2 p)).sum =
              4 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
                (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                  bitLift8 (R.rowCoefficientEntry rs.1 p) *
                    bitLift8 (R.rowCoefficientEntry rs.2 p)).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro rs _hrs
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro pq _hpq
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right, list_sum_map_mul_right]
        have hscale :
            ((unorderedPairs R.reducedRowIndexList).map fun rs =>
              4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                    bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                  bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                    bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum =
              4 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
                (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                  (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                      bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                    bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                      bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro rs _hrs
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring
private theorem lambdaSingle8_siteSum
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    2 * ((siteList Col).map fun p => R.lambdaSingle8 p * bitLift8 (f p)).sum =
      2 * ((siteList Col).map fun p =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r p)).sum) * bitLift8 (f p)).sum -
      4 * ((siteList Col).map fun p =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).sum) * bitLift8 (f p)).sum := by
  rw [mul_list_sum, mul_list_sum, mul_list_sum,
    List.map_map, List.map_map, List.map_map]
  rw [← list_sum_map_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _hp
  simp only [Function.comp_apply, lambdaSingle8]
  ring
private theorem lambdaPair8_sitePairSum
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    4 * ((sitePairList Col).map fun pq =>
      R.lambdaPair8 pq.1 pq.2 * bitLift8 (f pq.1) *
        bitLift8 (f pq.2)).sum =
      4 * ((sitePairList Col).map fun pq =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r pq.1) *
              bitLift8 (R.rowCoefficientEntry r pq.2)).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum -
      4 * ((sitePairList Col).map fun pq =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
              bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  rw [mul_list_sum, mul_list_sum, mul_list_sum,
    List.map_map, List.map_map, List.map_map]
  rw [← list_sum_map_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pq _hpq
  simp only [Function.comp_apply, lambdaPair8]
  ring
private theorem rowCliffordExponent8_physical_raw
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    R.rowCliffordExponent8 (R.rowCoefficientMap f) =
      2 * ((siteList Col).map fun p =>
        R.lambdaSingle8 p * bitLift8 (f p)).sum +
      4 * ((sitePairList Col).map fun pq =>
        R.lambdaPair8 pq.1 pq.2 * bitLift8 (f pq.1) *
          bitLift8 (f pq.2)).sum := by
  have hlinear :
      2 * R.rowGammaLinear8 (R.rowCoefficientMap f) R.reducedRowIndexList =
        (R.reducedRowIndexList.map fun r =>
          2 * (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientMap f r)).sum := by
    simp only [rowGammaLinear8]
    rw [mul_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _hr
    simp only [Function.comp_apply]
    ring
  have hquadratic :
      4 * R.rowGammaPair8 (R.rowCoefficientMap f) R.reducedRowIndexList =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientMap f rs.1) *
              bitLift8 (R.rowCoefficientMap f rs.2)).sum := by
    rw [R.rowGammaPair8_eq_unorderedPairs]
    rw [mul_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro rs _hrs
    simp only [Function.comp_apply]
    ring
  simp only [rowCliffordExponent8]
  rw [hlinear, hquadratic, R.linearCoordinates_sum_expand8 f,
    R.quadraticCoordinates_sum_expand8 f,
    R.lambdaSingle8_siteSum f, R.lambdaPair8_sitePairSum f]
  ring_nf
  have hnegFour (x : ZMod 8) : -(x * 4) = x * 4 := by
    calc
      -(x * 4) = x * (-4) := by ring
      _ = x * 4 := by rw [show (-4 : ZMod 8) = 4 by decide]
  simp only [sub_eq_add_neg]
  simp_rw [hnegFour]
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
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    R.rowCliffordExponent8 (R.rowCoefficientMap f) =
      2 * ((siteList Col).map fun p =>
        ((R.lambdaSingle p).val : ZMod 8) * bitLift8 (f p)).sum +
      4 * ((sitePairList Col).map fun pq =>
        ((R.lambdaPair pq.1 pq.2).val : ZMod 8) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  rw [R.rowCliffordExponent8_physical_raw f]
  apply congrArg₂ (· + ·)
  · rw [mul_list_sum, mul_list_sum, List.map_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    simp only [Function.comp_apply]
    calc
      2 * (R.lambdaSingle8 p * bitLift8 (f p)) =
          (2 * R.lambdaSingle8 p) * bitLift8 (f p) := by ring
      _ = (2 * ((R.lambdaSingle p).val : ZMod 8)) * bitLift8 (f p) := by
        rw [R.two_mul_lambdaSingle8 p]
      _ = 2 * (((R.lambdaSingle p).val : ZMod 8) * bitLift8 (f p)) := by ring
  · rw [mul_list_sum, mul_list_sum, List.map_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pq _hpq
    simp only [Function.comp_apply]
    calc
      4 * (R.lambdaPair8 pq.1 pq.2 * bitLift8 (f pq.1) *
          bitLift8 (f pq.2)) =
          (4 * R.lambdaPair8 pq.1 pq.2) * bitLift8 (f pq.1) *
            bitLift8 (f pq.2) := by ring
      _ = (4 * ((R.lambdaPair pq.1 pq.2).val : ZMod 8)) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2) := by
        rw [R.four_mul_lambdaPair8 pq.1 pq.2]
      _ = 4 * (((R.lambdaPair pq.1 pq.2).val : ZMod 8) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)) := by ring
end QEC.Distillation.Triorthogonal.BinaryRowFamily
