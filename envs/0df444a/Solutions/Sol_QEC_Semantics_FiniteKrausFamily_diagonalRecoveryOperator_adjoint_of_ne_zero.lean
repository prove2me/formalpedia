-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_adjoint_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:16:21.218428+00:00
-- url     : https://prove2.me/submissions/137ac57c-b57b-48dc-b6ac-88c41e2a0b20

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
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
omit [DecidableEq ι]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    {a : ι} (ha : lambda a ≠ 0) :
    LinearMap.adjoint (diagonalRecoveryOperator C F lambda a) =
      ((Real.sqrt (lambda a) : Complex)⁻¹) •
        (F.operator a).comp C.projector := by
  classical
  unfold diagonalRecoveryOperator
  rw [if_neg ha]
  let c : Complex := (Real.sqrt (lambda a) : Complex)⁻¹
  have hAdjS :
      LinearMap.adjoint (c • C.projector.comp (LinearMap.adjoint (F.operator a))) =
        star c • LinearMap.adjoint (C.projector.comp (LinearMap.adjoint (F.operator a))) :=
    map_smulₛₗ
      (LinearMap.adjoint : (Operator H) ≃ₗ⋆[Complex] Operator H)
      c (C.projector.comp (LinearMap.adjoint (F.operator a)))
  have hc : star c = c := by
    simp [c]
  calc
    LinearMap.adjoint (c • C.projector.comp (LinearMap.adjoint (F.operator a)))
        = star c • LinearMap.adjoint (C.projector.comp (LinearMap.adjoint (F.operator a))) :=
          hAdjS
    _ = c • (F.operator a).comp C.projector := by
          simp [hc, LinearMap.adjoint_comp, C.projector_adjoint_eq_self, c]
end QEC.Semantics.FiniteKrausFamily
