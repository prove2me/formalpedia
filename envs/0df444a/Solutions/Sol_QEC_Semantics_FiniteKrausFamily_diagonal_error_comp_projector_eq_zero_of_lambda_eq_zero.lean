-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:02.142486+00:00
-- url     : https://prove2.me/submissions/4edc3fa7-23fe-42b1-b223-dc00642a5861

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalProjectorConditionWithScalar_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
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
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    {i : ι} (hzero : lambda i = 0) :
    (F.operator i).comp C.projector = 0 := by
  let A : Operator H := (F.operator i).comp C.projector
  have hAdjComp : (LinearMap.adjoint A).comp A = 0 := by
    have hii := diagonalProjectorConditionWithScalar_apply hKL i i
    calc
      (LinearMap.adjoint A).comp A
          = (C.projector.comp
              ((LinearMap.adjoint (F.operator i)).comp (F.operator i))).comp
                C.projector := by
                ext x
                simp [A, LinearMap.adjoint_comp, C.projector_adjoint_eq_self,
                  LinearMap.comp_apply]
      _ = ((lambda i : Complex) • C.projector) := by
            simpa using hii
      _ = 0 := by
            simp [hzero]
  ext x
  have hxker : x ∈ LinearMap.ker ((LinearMap.adjoint A).comp A) := by
    simp [hAdjComp]
  have hxkerA : x ∈ LinearMap.ker A := by
    simpa [LinearMap.ker_adjoint_comp_self] using hxker
  simpa [A] using hxkerA
end QEC.Semantics.FiniteKrausFamily
