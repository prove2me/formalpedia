-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecovery_left_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:57.136672+00:00
-- url     : https://prove2.me/submissions/9a5625d4-0ff3-4021-a041-455b11089cd7

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalProjectorConditionWithScalar_apply
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
    (a : {i : ι // lambda i ≠ 0}) (i : ι) :
    (((((Real.sqrt (lambda a.1) : Complex)⁻¹) •
        C.projector.comp (LinearMap.adjoint (F.operator a.1))).comp
        ((F.operator i).comp C.projector)) : Operator H) =
      if a.1 = i then (Real.sqrt (lambda a.1) : Complex) • C.projector else 0 := by
  classical
  have hbranch := diagonalProjectorConditionWithScalar_apply hKL a.1 i
  have hsqrt_mul :
      ((Real.sqrt (lambda a.1) : Complex)⁻¹ * (lambda a.1 : Complex)) =
        (Real.sqrt (lambda a.1) : Complex) := by
    have hpos : 0 < lambda a.1 := lt_of_le_of_ne (hlambda_nonneg a.1) (Ne.symm a.2)
    have hsqrt_ne : (Real.sqrt (lambda a.1) : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hpos))
    have hsquare :
        (Real.sqrt (lambda a.1) : Complex) * (Real.sqrt (lambda a.1) : Complex) =
          (lambda a.1 : Complex) := by
      have hsquareR : Real.sqrt (lambda a.1) * Real.sqrt (lambda a.1) = lambda a.1 := by
        simpa [sq] using Real.sq_sqrt (hlambda_nonneg a.1)
      exact_mod_cast hsquareR
    rw [← hsquare]
    exact inv_mul_cancel_left₀ hsqrt_ne _
  by_cases hai : a.1 = i
  · subst i
    calc
      (((((Real.sqrt (lambda a.1) : Complex)⁻¹) •
          C.projector.comp (LinearMap.adjoint (F.operator a.1))).comp
          ((F.operator a.1).comp C.projector)) : Operator H)
          = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
              ((C.projector.comp
                ((LinearMap.adjoint (F.operator a.1)).comp (F.operator a.1))).comp
                  C.projector) := by
                ext x
                simp [LinearMap.comp_apply]
      _ = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
            ((lambda a.1 : Complex) • C.projector) := by
            rw [hbranch]
            simp
      _ = (Real.sqrt (lambda a.1) : Complex) • C.projector := by
            rw [smul_smul, hsqrt_mul]
      _ = if a.1 = a.1 then (Real.sqrt (lambda a.1) : Complex) • C.projector else 0 := by
            simp
  · calc
      (((((Real.sqrt (lambda a.1) : Complex)⁻¹) •
          C.projector.comp (LinearMap.adjoint (F.operator a.1))).comp
          ((F.operator i).comp C.projector)) : Operator H)
          = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
              ((C.projector.comp
                ((LinearMap.adjoint (F.operator a.1)).comp (F.operator i))).comp
                  C.projector) := by
                ext x
                simp [LinearMap.comp_apply]
      _ = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
            ((0 : Complex) • C.projector) := by
            rw [hbranch]
            simp [hai]
      _ = 0 := by
            simp
      _ = if a.1 = i then (Real.sqrt (lambda a.1) : Complex) • C.projector else 0 := by
            simp [hai]
end QEC.Semantics.FiniteKrausFamily
