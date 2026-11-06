-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.exists_recovery_of_diagonalProjectorConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:41.461135+00:00
-- url     : https://prove2.me/submissions/dbad0714-8dc4-4402-a7fc-38da62c65bb7

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_complete_diagonal_sum
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionSum_adjoint
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionSum_idempotent
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_branches
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionSum_residual
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_of_projectionSumRecoveryData
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
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    [DecidableEq ι]
    (F : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hF : F.Complete)
    {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j)) :
    ∃ recovery : QuantumChannel H H,
      FiniteKrausCorrectable ι H H C F recovery := by
  classical
  let R : ι → KrausOperator H H := fun a => diagonalRecoveryOperator C F lambda a
  let S : Operator H :=
    ∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)
  have hdiag_sum :
      (∑ i : ι, (lambda i : Complex)) • C.projector = C.projector :=
    by
      simpa [Matrix.diagonal_apply] using
        (indexedProjectorConditionWithScalar_complete_diagonal_sum hF hKL)
  exact exists_recovery_of_projectionSumRecoveryData
    (E := F) (C := C) hF R S
    (by rfl)
    (by
      change LinearMap.adjoint
          (∑ a : ι,
            (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
              (diagonalRecoveryOperator C F lambda a)) =
        ∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)
      exact diagonalRecoveryProjectionSum_adjoint F C lambda)
    (by
      change
        (∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)).comp
          (∑ a : ι,
            (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
              (diagonalRecoveryOperator C F lambda a)) =
        ∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)
      exact diagonalRecoveryProjectionSum_idempotent
        (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL)
    (by
      intro rho hρ
      exact diagonalRecoveryOperator_branches
        (F := F) (C := C) (lambda := lambda)
        hlambda_nonneg hKL hdiag_sum rho hρ)
    (by
      intro rho hρ
      exact diagonalRecoveryProjectionSum_residual
        (F := F) (C := C) (lambda := lambda)
        hlambda_nonneg hKL rho hρ)
end QEC.Semantics.FiniteKrausFamily
