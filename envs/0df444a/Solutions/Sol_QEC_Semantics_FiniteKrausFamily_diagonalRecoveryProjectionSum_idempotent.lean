-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:21.6972+00:00
-- url     : https://prove2.me/submissions/66da8aac-5e4e-49d3-b200-0177fcd25a53

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionTerm_mul
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
variable [DecidableEq ι]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j)) :
    (∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)).comp
      (∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)) =
    ∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a) := by
  classical
  let T : ι → Operator H := fun a =>
    (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
      (diagonalRecoveryOperator C F lambda a)
  calc
    (∑ a : ι, T a).comp (∑ b : ι, T b)
        = ∑ a : ι, ∑ b : ι, (T b).comp (T a) := by
            ext x
            simp [T, Finset.sum_apply, LinearMap.comp_apply]
    _ = ∑ a : ι, ∑ b : ι, if b = a then T b else 0 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            rw [diagonalRecoveryProjectionTerm_mul
              (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL b a]
    _ = ∑ a : ι, T a := by
            ext x
            simp [T]
end QEC.Semantics.FiniteKrausFamily
