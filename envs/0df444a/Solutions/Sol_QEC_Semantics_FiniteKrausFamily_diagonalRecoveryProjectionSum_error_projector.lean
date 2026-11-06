-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_error_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:33.641313+00:00
-- url     : https://prove2.me/submissions/3945f7e4-dad3-4d2c-a065-87fda5f6447d

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_branch
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_adjoint_of_ne_zero
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_idempotent
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
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (i : ι) :
    (∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)).comp
        ((F.operator i).comp C.projector) =
      (F.operator i).comp C.projector := by
  classical
  let R : ι → Operator H := fun a => diagonalRecoveryOperator C F lambda a
  let T : ι → Operator H := fun a => (LinearMap.adjoint (R a)).comp (R a)
  by_cases hi0 : lambda i = 0
  · have hzero := diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
      (F := F) (C := C) (lambda := lambda) hKL hi0
    rw [hzero]
    ext x
    simp
  · have hipos : 0 < lambda i := lt_of_le_of_ne (hlambda_nonneg i) (Ne.symm hi0)
    have hsqrt_pos_R : 0 < Real.sqrt (lambda i) := Real.sqrt_pos.2 hipos
    have hsqrt_ne_R : Real.sqrt (lambda i) ≠ 0 := ne_of_gt hsqrt_pos_R
    have hsqrt_ne_C : (Real.sqrt (lambda i) : Complex) ≠ 0 := by
      exact_mod_cast hsqrt_ne_R
    have hadj := diagonalRecoveryOperator_adjoint_of_ne_zero
      (F := F) (C := C) (lambda := lambda) (a := i) hi0
    have hbranch := diagonalRecoveryOperator_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL
    calc
      (∑ a : ι, T a).comp ((F.operator i).comp C.projector)
          = ∑ a : ι, (LinearMap.adjoint (R a)).comp
              ((R a).comp ((F.operator i).comp C.projector)) := by
              ext x
              simp [T, R, Finset.sum_apply, LinearMap.comp_apply]
      _ = ∑ a : ι, (LinearMap.adjoint (R a)).comp
              (if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0) := by
              apply Finset.sum_congr rfl
              intro a _ha
              rw [hbranch a i]
      _ = (LinearMap.adjoint (R i)).comp
              ((Real.sqrt (lambda i) : Complex) • C.projector) := by
              simpa using
                (Finset.sum_eq_single (s := Finset.univ)
                  (f := fun a : ι =>
                    (LinearMap.adjoint (R a)).comp
                      (if a = i then
                        (Real.sqrt (lambda a) : Complex) • C.projector
                      else 0))
                  i
                  (by
                    intro b _hb hbi
                    simp [hbi])
                  (by
                    intro hi
                    simp at hi))
      _ = (F.operator i).comp C.projector := by
              change (LinearMap.adjoint (diagonalRecoveryOperator C F lambda i)).comp
                  ((Real.sqrt (lambda i) : Complex) • C.projector) =
                (F.operator i).comp C.projector
              rw [hadj]
              ext x
              have hscalar :
                  ((Real.sqrt (lambda i) : Complex)⁻¹) *
                      (Real.sqrt (lambda i) : Complex) = 1 :=
                inv_mul_cancel₀ hsqrt_ne_C
              have hP := congrArg (fun A : Operator H => A x) C.projector_idempotent
              simp [LinearMap.comp_apply]
              rw [show C.projector (C.projector x) = C.projector x by
                simpa [LinearMap.comp_apply] using hP]
              change ((Real.sqrt (lambda i) : Complex)⁻¹) •
                  ((Real.sqrt (lambda i) : Complex) •
                    (F.operator i) (C.projector x)) =
                (F.operator i) (C.projector x)
              rw [smul_smul, hscalar]
              simp
end QEC.Semantics.FiniteKrausFamily
