-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:30.28984+00:00
-- url     : https://prove2.me/submissions/675f9ed0-9628-4196-9a18-0b37d38d43e9

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_branch
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_adjoint_of_ne_zero
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
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a b : ι) :
    (diagonalRecoveryOperator C F lambda a).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda b)) =
      if a = b then
        if lambda a = 0 then 0 else C.projector
      else 0 := by
  classical
  by_cases hb : lambda b = 0
  · unfold diagonalRecoveryOperator
    rw [if_pos hb]
    by_cases hab : a = b
    · subst a
      simp [hb]
    · simp [hab]
  · have hbpos : 0 < lambda b := lt_of_le_of_ne (hlambda_nonneg b) (Ne.symm hb)
    have hsqrt_pos_R : 0 < Real.sqrt (lambda b) := Real.sqrt_pos.2 hbpos
    have hsqrt_ne_R : Real.sqrt (lambda b) ≠ 0 :=
      ne_of_gt hsqrt_pos_R
    have hsqrt_ne_C : (Real.sqrt (lambda b) : Complex) ≠ 0 := by
      exact_mod_cast hsqrt_ne_R
    have hAdj := diagonalRecoveryOperator_adjoint_of_ne_zero
      (F := F) (C := C) (lambda := lambda) (a := b) hb
    have hbranch := diagonalRecoveryOperator_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a b
    rw [hAdj]
    calc
      (diagonalRecoveryOperator C F lambda a).comp
          (((Real.sqrt (lambda b) : Complex)⁻¹) •
            (F.operator b).comp C.projector)
          = ((Real.sqrt (lambda b) : Complex)⁻¹) •
              ((diagonalRecoveryOperator C F lambda a).comp
                ((F.operator b).comp C.projector)) := by
              ext x
              simp [LinearMap.comp_apply]
      _ = ((Real.sqrt (lambda b) : Complex)⁻¹) •
            (if a = b then (Real.sqrt (lambda a) : Complex) • C.projector else 0) := by
              rw [hbranch]
      _ = if a = b then
            if lambda a = 0 then 0 else C.projector
          else 0 := by
              by_cases hab : a = b
              · subst a
                simp [hb]
                ext x
                change ((Real.sqrt (lambda b) : Complex)⁻¹) •
                    ((Real.sqrt (lambda b) : Complex) • C.projector x) =
                  C.projector x
                rw [smul_smul, inv_mul_cancel₀ hsqrt_ne_C]
                simp
              · simp [hab]
end QEC.Semantics.FiniteKrausFamily
