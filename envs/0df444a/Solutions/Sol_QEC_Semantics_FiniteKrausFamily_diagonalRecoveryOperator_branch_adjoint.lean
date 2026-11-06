-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_branch_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:29.632246+00:00
-- url     : https://prove2.me/submissions/de1f79cb-b76f-47c6-9292-83fd68ec908d

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_branch
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
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a i : ι) :
    (C.projector.comp (LinearMap.adjoint (F.operator i))).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)) =
      if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0 := by
  classical
  have h := congrArg LinearMap.adjoint
    (diagonalRecoveryOperator_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a i)
  by_cases hai : a = i
  · subst a
    have hR :
        LinearMap.adjoint
            (if i = i then (Real.sqrt (lambda i) : Complex) • C.projector else 0) =
          (Real.sqrt (lambda i) : Complex) • C.projector := by
      calc
        LinearMap.adjoint
            (if i = i then (Real.sqrt (lambda i) : Complex) • C.projector else 0)
            = LinearMap.adjoint ((Real.sqrt (lambda i) : Complex) • C.projector) := by
              simp
        _ = star (Real.sqrt (lambda i) : Complex) • LinearMap.adjoint C.projector := by
              exact map_smulₛₗ
                (LinearMap.adjoint : (Operator H) ≃ₗ⋆[Complex] Operator H)
                (Real.sqrt (lambda i) : Complex) C.projector
        _ = (Real.sqrt (lambda i) : Complex) • C.projector := by
              simp [C.projector_adjoint_eq_self]
    simpa [LinearMap.adjoint_comp, C.projector_adjoint_eq_self] using h.trans hR
  · have hR :
        LinearMap.adjoint
            (if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0) =
          0 := by
      simp [hai]
    simpa [hai, LinearMap.adjoint_comp, C.projector_adjoint_eq_self] using h.trans hR
end QEC.Semantics.FiniteKrausFamily
