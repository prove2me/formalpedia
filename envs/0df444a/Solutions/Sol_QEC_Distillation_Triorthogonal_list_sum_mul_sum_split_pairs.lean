-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.list_sum_mul_sum_split_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:50:55.763277+00:00
-- url     : https://prove2.me/submissions/0b5a3546-773c-4f4c-9461-b74bb486a698

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
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
private theorem list_sum_mul_sum_split_cross {A R : Type*} [CommRing R]
    (xs : List A) (f g : A → R) :
    (xs.map f).sum * (xs.map g).sum =
      (xs.map fun x => f x * g x).sum + pairMulCrossSum f g xs := by
  induction xs with
  | nil => simp [pairMulCrossSum]
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, pairMulCrossSum]
      have hf : f x * (xs.map g).sum = (xs.map fun y => f x * g y).sum :=
        by simpa [List.map_map, Function.comp_def] using mul_list_sum (f x) (xs.map g)
      have hg : (xs.map f).sum * g x = (xs.map fun y => f y * g x).sum := by
        rw [mul_comm]
        simpa [mul_comm, List.map_map, Function.comp_def] using mul_list_sum (g x) (xs.map f)
      calc
        (f x + (xs.map f).sum) * (g x + (xs.map g).sum) =
            f x * g x + f x * (xs.map g).sum +
              (xs.map f).sum * g x + (xs.map f).sum * (xs.map g).sum := by ring
        _ = f x * g x + (xs.map fun x => f x * g x).sum +
              ((xs.map fun y => f x * g y + f y * g x).sum +
                pairMulCrossSum f g xs) := by
              rw [ih, hf, hg, list_sum_map_add]
              ring
private theorem pairMulCrossSum_eq_unorderedPairs {A R : Type*} [CommRing R]
    (xs : List A) (f g : A → R) :
    pairMulCrossSum f g xs =
      ((unorderedPairs xs).map fun pq =>
        f pq.1 * g pq.2 + f pq.2 * g pq.1).sum := by
  induction xs with
  | nil => simp [pairMulCrossSum, unorderedPairs]
  | cons x xs ih =>
      simp only [pairMulCrossSum, unorderedPairs, List.map_append,
        List.sum_append, List.map_map, ih]
      rfl
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
theorem _root_.solution {A R : Type*} [CommRing R]
    (xs : List A) (f g : A → R) :
    (xs.map f).sum * (xs.map g).sum =
      (xs.map fun x => f x * g x).sum +
        ((unorderedPairs xs).map fun pq =>
          f pq.1 * g pq.2 + f pq.2 * g pq.1).sum := by
  rw [list_sum_mul_sum_split_cross, pairMulCrossSum_eq_unorderedPairs]
end QEC.Distillation.Triorthogonal
