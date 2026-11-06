-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:44.459717+00:00
-- url     : https://prove2.me/submissions/86e18f52-1377-43c9-a8a1-baeb18aa34c3

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecovery_left_branch
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
    (a i : ι) :
    ((diagonalRecoveryOperator C F lambda a).comp
        ((F.operator i).comp C.projector) : Operator H) =
      if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0 := by
  classical
  by_cases hzero : lambda a = 0
  · by_cases hai : a = i
    · subst i
      simp [diagonalRecoveryOperator, hzero]
    · simp [diagonalRecoveryOperator, hzero, hai]
  · let aa : {i : ι // lambda i ≠ 0} := ⟨a, hzero⟩
    have hsub := diagonalRecovery_left_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL aa i
    simpa [diagonalRecoveryOperator, hzero, aa] using hsub
end QEC.Semantics.FiniteKrausFamily
